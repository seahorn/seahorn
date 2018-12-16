// Symbolic execution (loosely) based on semantics used in UFO
#include "llvm/IR/GetElementPtrTypeIterator.h"

#include "seahorn/BvOpSem2.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "ufo/ufo_iterators.hpp"
#include "llvm/Support/CommandLine.h"


using namespace seahorn;
using namespace llvm;
using namespace ufo;

static llvm::cl::opt<bool> GlobalConstraints2(
    "horn-bv2-global-constraints",
    llvm::cl::desc("Maximize the use of global (i.e., unguarded) constraints"),
    cl::init(false));

static llvm::cl::opt<bool> EnableUniqueScalars2(
    "horn-bv2-singleton-aliases",
    llvm::cl::desc("Treat singleton alias sets as scalar values"),
    cl::init(true));

static llvm::cl::opt<bool> InferMemSafety2(
    "horn-bv2-use-mem-safety",
    llvm::cl::desc("Rely on memory safety assumptions such as "
                   "successful load/store imply validity of their arguments"),
    cl::init(true), cl::Hidden);

static llvm::cl::opt<bool> IgnoreCalloc2(
    "horn-bv2-ignore-calloc",
    llvm::cl::desc(
        "Treat calloc same as malloc, ignore that memory is initialized"),
    cl::init(false), cl::Hidden);

static llvm::cl::opt<bool>
    UseWrite2("horn-bv2-use-write",
             llvm::cl::desc("Write to store instead of havoc"), cl::init(false),
             cl::Hidden);

static llvm::cl::opt<bool>
    PartMem2("horn-bv2-part-mem",
            llvm::cl::desc(
                "Add constraints to partition memory into disjoint segments"),
            cl::init(false), cl::Hidden);

static llvm::cl::opt<unsigned>
    PartMemSize2("horn-bv2-part-mem-size",
                llvm::cl::desc("Maximum memory region size in KB"), cl::init(4),
                cl::Hidden);

static llvm::cl::opt<bool> EnableModelExternalCalls2(
    "horn-bv2-enable-external-calls",
    llvm::cl::desc("Model external function call as an uninterpreted function"),
    llvm::cl::init(false));

static llvm::cl::list<std::string> IgnoreExternalFunctions2(
    "horn-bv2-ignore-external-functions",
    llvm::cl::desc(
        "These functions are not modeled as uninterpreted functions"),
    llvm::cl::ZeroOrMore, llvm::cl::CommaSeparated);

static const Value *extractUniqueScalar(CallSite &cs) {
  if (!EnableUniqueScalars2)
    return nullptr;
  else
    return seahorn::shadow_dsa::extractUniqueScalar(cs);
}

static const Value *extractUniqueScalar(const CallInst *ci) {
  if (!EnableUniqueScalars2)
    return nullptr;
  else
    return seahorn::shadow_dsa::extractUniqueScalar(ci);
}

static bool isShadowMem(const Value &V, const Value **out) {
  const Value *scalar;
  bool res = seahorn::shadow_dsa::isShadowMem(V, &scalar);
  if (EnableUniqueScalars2 && out)
    *out = scalar;
  return res;
}

namespace {
struct OpSemBase {
  SymStore &m_s;
  ExprFactory &m_efac;
  Bv2OpSem &m_sem;
  ExprVector &m_side;

  Expr trueE;
  Expr falseE;
  Expr zeroE;
  Expr oneE;
  Expr trueBv;
  Expr falseBv;
  Expr nullBv;

  /// -- start of current memory segment
  Expr m_cur_startMem;
  /// -- end of current memory segment
  Expr m_cur_endMem;

  Expr m_largestPtr;

  /// -- current read memory
  Expr m_inMem;
  /// -- current write memory
  Expr m_outMem;
  /// --- true if the current read/write is to unique memory location
  bool m_uniq;

  /// -- parameters for a function call
  ExprVector m_fparams;

  Expr m_activeLit;

  OpSemBase(SymStore &s, Bv2OpSem &sem, ExprVector &side)
      : m_s(s), m_efac(m_s.getExprFactory()), m_sem(sem), m_side(side),
        m_cur_startMem(nullptr), m_cur_endMem(nullptr), m_largestPtr(nullptr),
        m_inMem(nullptr), m_outMem(nullptr) {
    trueE = mk<TRUE>(m_efac);
    falseE = mk<FALSE>(m_efac);

    zeroE = mkTerm<mpz_class>(0, m_efac);
    oneE = mkTerm<mpz_class>(1, m_efac);
    trueBv = bv::bvnum(1, 1, m_efac);
    falseBv = bv::bvnum(0, 1, m_efac);
    nullBv = bv::bvnum(0, m_sem.pointerSizeInBits(), m_efac);
    m_uniq = false;
    resetActiveLit();

    mpz_class val;
    if (ptrSz() == 64) {
      val = 0x000000000FFFFFFF;
    } else if (ptrSz() == 32) {
      val = 0x0FFFFFFF;
    } else {
      assert(false && "Unexpected pointer size");
    }
    m_largestPtr = bv::bvnum(val, ptrSz(), m_efac);
    // -- first two arguments are reserved for error flag
    m_fparams.push_back(falseE);
    m_fparams.push_back(falseE);
    m_fparams.push_back(falseE);
  }

  Expr memStart(unsigned id) { return m_sem.memStart(id); }
  Expr memEnd(unsigned id) { return m_sem.memEnd(id); }
  Expr symb(const Value &I) { return m_sem.symb(I); }
  unsigned ptrSz() { return m_sem.pointerSizeInBits(); }

  Expr read(const Value &v) {
    return m_sem.isTracked(v) ? m_s.read(symb(v)) : Expr(0);
  }

  Expr lookup(const Value &v) { return m_sem.lookup(m_s, v); }
  Expr havoc(const Value &v) {
    return m_sem.isTracked(v) ? m_s.havoc(symb(v)) : Expr(0);
  }
  void write(const Value &v, Expr val) {
    if (val && m_sem.isTracked(v))
      m_s.write(symb(v), val);
  }

  void resetActiveLit() { m_activeLit = trueE; }
  void setActiveLit(Expr act) { m_activeLit = act; }

  // -- add conditional side condition
  void addCondSide(Expr c) { side(c, true); }

  void side(Expr v, bool conditional = false) {
    if (!v)
      return;
    if (!GlobalConstraints2 || conditional)
      m_side.push_back(boolop::limp(m_activeLit, v));
    else
      m_side.push_back(v);
  }

  void bside(Expr lhs, Expr rhs, bool conditional = false) {
    if (lhs && rhs)
      side(mk<IFF>(lhs, rhs), conditional);
  }

  void side(Expr lhs, Expr rhs, bool conditional = false) {
    if (lhs && rhs)
      side(mk<EQ>(lhs, rhs), conditional);
  }

  /// convert bv1 to bool
  Expr bvToBool(Expr bv) {
    if (bv == trueBv)
      return trueE;
    if (bv == falseBv)
      return falseE;
    return mk<EQ>(bv, trueBv);
  }
  Expr boolToBv(Expr b) {
    if (isOpX<TRUE>(b))
      return trueBv;
    if (isOpX<FALSE>(b))
      return falseBv;
    return mk<ITE>(b, trueBv, falseBv);
  }
};

struct OpSemVisitor : public InstVisitor<OpSemVisitor>, OpSemBase {
  OpSemVisitor(SymStore &s, Bv2OpSem &sem, ExprVector &side)
      : OpSemBase(s, sem, side) {}

  void addAlignConstraint(Expr e, unsigned sz) {
    switch (sz) {
    case 4:
      side(mk<EQ>(bv::extract(2 - 1, 0, e), bv::bvnum(0, 2, m_efac)));
      break;
    case 8:
      side(mk<EQ>(bv::extract(3 - 1, 0, e), bv::bvnum(0, 3, m_efac)));
      break;
    default:
      // FIXME: expensive encoding
      side(mk<EQ>(mk<BUREM>(e, bv::bvnum(sz, ptrSz(), m_efac)),
                  bv::bvnum(0, ptrSz(), m_efac)));
    }
  }

  /// base case. if all else fails.
  void visitInstruction(Instruction &I) { havoc(I); }

  /// skip PHI nodes
  void visitPHINode(PHINode &I) { /* do nothing */
  }

  void visitCmpInst(CmpInst &I) {
    Expr lhs = havoc(I);

    const Value &v0 = *I.getOperand(0);
    const Value &v1 = *I.getOperand(1);

    Expr op0 = lookup(v0);
    Expr op1 = lookup(v1);

    if (!(op0 && op1))
      return;

    Expr rhs;

    switch (I.getPredicate()) {
    case CmpInst::ICMP_EQ:
      rhs = mk<EQ>(op0, op1);
      break;
    case CmpInst::ICMP_NE:
      rhs = mk<NEQ>(op0, op1);
      break;
    case CmpInst::ICMP_UGT:
      rhs = mk<BUGT>(op0, op1);
      break;
    case CmpInst::ICMP_SGT:
      if (v0.getType()->isIntegerTy(1)) {
        if (isOpX<TRUE>(op1))
          // icmp sgt op0, i1 true  == !op0
          rhs = boolop::lneg(op0);
        else
          rhs = bvToBool(mk<BSGT>(boolToBv(op0), boolToBv(op1)));
      } else
        rhs = mk<BSGT>(op0, op1);
      break;
    case CmpInst::ICMP_UGE:
      rhs = mk<BUGE>(op0, op1);
      break;
    case CmpInst::ICMP_SGE:
      rhs = mk<BSGE>(op0, op1);
      break;
    case CmpInst::ICMP_ULT:
      rhs = mk<BULT>(op0, op1);
      break;
    case CmpInst::ICMP_SLT:
      rhs = mk<BSLT>(op0, op1);
      break;
    case CmpInst::ICMP_ULE:
      rhs = mk<BULE>(op0, op1);
      break;
    case CmpInst::ICMP_SLE:
      rhs = mk<BSLE>(op0, op1);
      break;
    default:
      break;
    }

    if (UseWrite2)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitSelectInst(SelectInst &I) {
    if (!m_sem.isTracked(I))
      return;

    Expr lhs = havoc(I);
    Expr cond = lookup(*I.getCondition());
    Expr op0 = lookup(*I.getTrueValue());
    Expr op1 = lookup(*I.getFalseValue());

    if (cond && op0 && op1) {
      Expr rhs = mk<ITE>(cond, op0, op1);
      if (UseWrite2)
        write(I, rhs);
      else
        side(lhs, rhs);
    }
  }

  void visitBinaryOperator(BinaryOperator &I) {
    if (!m_sem.isTracked(I))
      return;

    const Value &v0 = *(I.getOperand(0));
    const Value &v1 = *(I.getOperand(1));

    Expr op0 = lookup(v0);
    Expr op1 = lookup(v1);
    if (!(op0 && op1))
      return;

    Expr lhs = havoc(I);
    Expr rhs;
    switch (I.getOpcode()) {
    case BinaryOperator::Add:
      rhs = mk<BADD>(op0, op1);
      break;
    case BinaryOperator::Sub:
      rhs = mk<BSUB>(op0, op1);
      break;
    case BinaryOperator::Mul:
      rhs = mk<BMUL>(op0, op1);
      break;
    case BinaryOperator::UDiv:
      rhs = mk<BUDIV>(op0, op1);
      break;
    case BinaryOperator::SDiv:
      rhs = mk<BSDIV>(op0, op1);
      break;
    case BinaryOperator::Shl:
      rhs = mk<BSHL>(op0, op1);
      break;
    case BinaryOperator::AShr:
      rhs = mk<BASHR>(op0, op1);
      break;
    case BinaryOperator::SRem:
      rhs = mk<BSREM>(op0, op1);
      break;
    case BinaryOperator::URem:
      rhs = mk<BUREM>(op0, op1);
      break;
    case BinaryOperator::And:
      if (v0.getType()->isIntegerTy(1) && v1.getType()->isIntegerTy(1))
        rhs = mk<AND>(op0, op1);
      else
        rhs = mk<BAND>(op0, op1);
      break;
    case BinaryOperator::Or:
      if (v0.getType()->isIntegerTy(1) && v1.getType()->isIntegerTy(1))
        rhs = mk<OR>(op0, op1);
      else
        rhs = mk<BOR>(op0, op1);
      break;
    case BinaryOperator::Xor:
      if (v0.getType()->isIntegerTy(1) && v1.getType()->isIntegerTy(1))
        rhs = mk<XOR>(op0, op1);
      else
        rhs = mk<BXOR>(op0, op1);
      break;
    case BinaryOperator::LShr:
      rhs = mk<BLSHR>(op0, op1);
      break;
    default:
      break;
    }

    if (UseWrite2)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitReturnInst(ReturnInst &I) {
    // -- skip return argument of main
    if (I.getParent()->getParent()->getName().equals("main"))
      return;

    if (I.getNumOperands() > 0)
      lookup(*I.getOperand(0));
  }

  void visitBranchInst(BranchInst &I) {
    if (I.isConditional())
      lookup(*I.getCondition());
  }

  void visitTruncInst(TruncInst &I) {
    if (!m_sem.isTracked(I))
      return;
    Expr lhs = havoc(I);
    Expr op0 = lookup(*I.getOperand(0));

    if (!op0)
      return;

    uint64_t width = m_sem.sizeInBits(I);
    Expr rhs = bv::extract(width - 1, 0, op0);

    if (I.getType()->isIntegerTy(1))
      rhs = bvToBool(rhs);

    if (UseWrite2)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitZExtInst(ZExtInst &I) {
    if (!m_sem.isTracked(I))
      return;
    Expr lhs = havoc(I);
    Expr op0 = lookup(*I.getOperand(0));
    if (!op0)
      return;

    if (I.getOperand(0)->getType()->isIntegerTy(1))
      op0 = boolToBv(op0);

    Expr rhs = bv::zext(op0, m_sem.sizeInBits(I));
    if (UseWrite2)
      write(I, rhs);
    else
      side(lhs, rhs);
  }
  void visitSExtInst(SExtInst &I) {
    if (!m_sem.isTracked(I))
      return;
    Expr lhs = havoc(I);
    Expr op0 = lookup(*I.getOperand(0));
    if (!op0)
      return;

    if (I.getOperand(0)->getType()->isIntegerTy(1))
      op0 = boolToBv(op0);

    Expr rhs = bv::sext(op0, m_sem.sizeInBits(I));
    if (UseWrite2)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitPtrToIntInst(PtrToIntInst &I) {
    if (!m_sem.isTracked(I))
      return;
    Expr lhs = havoc(I);
    Expr op0 = lookup(*I.getOperand(0));
    if (!op0)
      return;

    uint64_t dsz = m_sem.sizeInBits(I);
    uint64_t ssz = m_sem.sizeInBits(*I.getOperand(0));

    Expr rhs;

    if (dsz == ssz)
      rhs = op0;
    else if (dsz > ssz)
      rhs = bv::zext(op0, dsz);
    else
      rhs = bv::extract(dsz - 1, 0, op0);

    if (UseWrite2)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitIntToPtrInst(IntToPtrInst &I) {
    if (!m_sem.isTracked(I))
      return;
    Expr lhs = havoc(I);
    Expr op0 = lookup(*I.getOperand(0));
    if (!op0)
      return;

    uint64_t dsz = m_sem.sizeInBits(I);
    uint64_t ssz = m_sem.sizeInBits(*I.getOperand(0));

    Expr rhs;

    if (dsz == ssz)
      rhs = op0;
    else if (dsz > ssz)
      rhs = bv::zext(op0, dsz);
    else
      rhs = bv::extract(dsz - 1, 0, op0);

    if (UseWrite2)
      write(I, rhs);
    else
      side(lhs, rhs);
  }

  void visitGetElementPtrInst(GetElementPtrInst &gep) {

    if (!m_sem.isTracked(gep))
      return;
    Expr lhs = havoc(gep);

    Value *ptrOp = gep.getPointerOperand();
    Expr base = lookup(*ptrOp);
    if (!base)
      return;

    Expr off = m_sem.symbolicIndexedOffset(m_s, gep);
    if (!off)
      return;

    if (UseWrite2)
      write(gep, mk<BADD>(base, off));
    else
      side(lhs, mk<BADD>(base, off));

    if (InferMemSafety2) {
      // -- extra constraints that exclude undefined behavior
      if (!gep.isInBounds() || gep.getPointerAddressSpace() != 0)
        return;
      // -- base > 0 -> lhs > 0
      // side (mk<OR> (mk<EQ> (base, nullBv),
      // mk<NEQ> (read (gep), nullBv)), true);

      // lhs >= base
      side(mk<BUGE>(read(gep), base));
    }
  }

  void visitCallSite(CallSite CS) {
    assert(CS.isCall());
    const Function *f = CS.getCalledFunction();

    Instruction &I = *CS.getInstruction();
    BasicBlock &BB = *I.getParent();

    // -- unknown/indirect function call
    if (!f) {
      // XXX Use DSA and/or Devirt to handle better
      assert(m_fparams.size() == 3);
      visitInstruction(I);
      return;
    }

    const Function &F = *f;
    const Function &PF = *I.getParent()->getParent();

    // skip intrinsic functions
    if (F.isIntrinsic()) {
      assert(m_fparams.size() == 3);
      return;
    }

    if (F.getName().startswith("verifier.assume")) {
      Expr c = lookup(*CS.getArgument(0));
      if (F.getName().equals("verifier.assume.not"))
        c = boolop::lneg(c);

      assert(m_fparams.size() == 3);
      // -- assumption is only active when error flag is false
      if (!isOpX<TRUE>(c))
        addCondSide(boolop::lor(m_s.read(m_sem.errorFlag(BB)), c));
    } else if (F.getName().equals("calloc") && m_inMem && m_outMem &&
               m_sem.isTracked(I)) {
      havoc(I);
      assert(m_fparams.size() == 3);
      assert(!m_uniq);

      if (IgnoreCalloc2)
        m_side.push_back(mk<EQ>(m_outMem, m_inMem));
      else {
        // XXX This is potentially unsound if the corresponding DSA
        // XXX node corresponds to multiple allocation sites
        errs() << "WARNING: zero-initializing DSA node due to calloc()\n";
        side(m_outMem,
             op::array::constArray(bv::bvsort(ptrSz(), m_efac), nullBv));
      }
    }

    else if (m_sem.hasFunctionInfo(F)) {
      const FunctionInfo &fi = m_sem.getFunctionInfo(F);

      // enabled
      m_fparams[0] = m_activeLit; // activation literal
      // error flag in
      m_fparams[1] = (m_s.read(m_sem.errorFlag(BB)));
      // error flag out
      m_fparams[2] = (m_s.havoc(m_sem.errorFlag(BB)));
      for (const Argument *arg : fi.args)
        m_fparams.push_back(m_s.read(symb(*CS.getArgument(arg->getArgNo()))));
      for (const GlobalVariable *gv : fi.globals)
        m_fparams.push_back(m_s.read(symb(*gv)));

      if (fi.ret)
        m_fparams.push_back(m_s.havoc(symb(I)));

      LOG("arg_error", if (m_fparams.size() != bind::domainSz(fi.sumPred)) {
        errs() << "Call instruction: " << I << "\n";
        errs() << "Caller: " << PF << "\n";
        errs() << "Callee: " << F << "\n";
        // errs () << "Sum predicate: " << *fi.sumPred << "\n";
        errs() << "m_fparams.size: " << m_fparams.size() << "\n";
        errs() << "Domain size: " << bind::domainSz(fi.sumPred) << "\n";
        errs() << "m_fparams\n";
        for (auto r : m_fparams)
          errs() << *r << "\n";
        errs() << "regions: " << fi.regions.size()
               << " args: " << fi.args.size()
               << " globals: " << fi.globals.size() << " ret: " << fi.ret
               << "\n";
        errs() << "regions\n";
        for (auto r : fi.regions)
          errs() << *r << "\n";
        errs() << "args\n";
        for (auto r : fi.args)
          errs() << *r << "\n";
        errs() << "globals\n";
        for (auto r : fi.globals)
          errs() << *r << "\n";
        if (fi.ret)
          errs() << "ret: " << *fi.ret << "\n";
      });

      assert(m_fparams.size() == bind::domainSz(fi.sumPred));
      m_side.push_back(bind::fapp(fi.sumPred, m_fparams));

      m_fparams.clear();
      m_fparams.push_back(falseE);
      m_fparams.push_back(falseE);
      m_fparams.push_back(falseE);
    } else if (F.getName().startswith("shadow.mem") && m_sem.isTracked(I)) {
      if (F.getName().equals("shadow.mem.init")) {
        m_s.havoc(symb(I));
        unsigned id = shadow_dsa::getShadowId(CS);
        assert(id >= 0);

        // -- add constraints only if asked
        if (PartMem2) {

          Expr memStartE = memStart(id);
          Expr memEndE = memEnd(id);
          memStartE = m_s.havoc(memStartE);
          memEndE = m_s.havoc(memEndE);

          // -- start < end
          side(mk<BULT>(memStartE, memEndE));

          // -- end < largestPtr
          side(mk<BULT>(memEndE, m_largestPtr));

          if (PartMemSize2 > 0) {
            // -- end - start <= PartMemSize2 KB
            side(mk<BULE>(mk<BSUB>(memEndE, memStartE),
                          bv::bvnum(PartMemSize2 * 1024, ptrSz(), m_efac)));
          }

          // -- old_end < new_start
          if (m_cur_endMem)
            side(mk<BULT>(m_s.read(m_cur_endMem), memStartE));

          // -- remember last choice
          m_cur_startMem = memStart(id);
          m_cur_endMem = memEnd(id);

          /// start addresses are aligned:
          ///   In addition to enforce that all pointers are
          ///   aligned, we also need to enforce that the start
          ///   address is also aligned.
          addAlignConstraint(memStartE, ptrSz() / 8 /*bytes*/);
        }

      } else if (F.getName().equals("shadow.mem.load")) {
        const Value &v = *CS.getArgument(1);
        m_inMem = m_s.read(symb(v));
        m_uniq = extractUniqueScalar(CS) != nullptr;
        if (PartMem2) {
          m_cur_startMem = memStart(shadow_dsa::getShadowId(CS));
          m_cur_endMem = memEnd(shadow_dsa::getShadowId(CS));
        }
      } else if (F.getName().equals("shadow.mem.store")) {
        m_inMem = m_s.read(symb(*CS.getArgument(1)));
        m_outMem = m_s.havoc(symb(I));
        m_uniq = extractUniqueScalar(CS) != nullptr;
        if (PartMem2) {
          m_cur_startMem = memStart(shadow_dsa::getShadowId(CS));
          m_cur_endMem = memEnd(shadow_dsa::getShadowId(CS));
        }
      } else if (F.getName().equals("shadow.mem.arg.ref"))
        m_fparams.push_back(m_s.read(symb(*CS.getArgument(1))));
      else if (F.getName().equals("shadow.mem.arg.mod")) {
        m_fparams.push_back(m_s.read(symb(*CS.getArgument(1))));
        m_fparams.push_back(m_s.havoc(symb(I)));
      } else if (F.getName().equals("shadow.mem.arg.new"))
        m_fparams.push_back(m_s.havoc(symb(I)));
      else if (!PF.getName().equals("main") &&
               F.getName().equals("shadow.mem.in")) {
        m_s.read(symb(*CS.getArgument(1)));
      } else if (!PF.getName().equals("main") &&
                 F.getName().equals("shadow.mem.out")) {
        m_s.read(symb(*CS.getArgument(1)));
      } else if (!PF.getName().equals("main") &&
                 F.getName().equals("shadow.mem.arg.init")) {
        // regions initialized in main are global. We want them to
        // flow to the arguments
        /* do nothing */
      }
    } else {
      if (f->isDeclaration() &&
          !f->getFunctionType()->getReturnType()->isVoidTy() &&
          m_sem.isTracked(I) &&
          // we model external calls as interpreted functions
          EnableModelExternalCalls2 &&
          // user didn't say to ignore the function in particular
          (std::find(IgnoreExternalFunctions2.begin(),
                     IgnoreExternalFunctions2.end(),
                     f->getName()) == IgnoreExternalFunctions2.end())) {

        // Treat the call as an uninterpreted function
        Expr lhs = havoc(I);
        ExprVector fargs;
        ExprVector sorts;
        fargs.reserve(CS.arg_size());
        sorts.reserve(CS.arg_size());
        bool cannot_infer_types = false;
        for (auto &a : CS.args()) {
          if (!m_sem.isTracked(*a)) {
            continue;
          }
          Expr e = lookup(*a);
          fargs.push_back(e);
          Expr s = bind::typeOf(e);
          if (!s) {
            // bind::typeOf is partially defined
            cannot_infer_types = true;
            break;
          }
          sorts.push_back(s);
        }
        if (!cannot_infer_types) {
          // return type of the function
          Expr lhs_ty = bind::typeOf(lhs);
          if (!lhs_ty) {
            cannot_infer_types = true;
          } else {
            sorts.push_back(lhs_ty);
          }
        }

        if (cannot_infer_types) {
          fargs.clear();
          sorts.clear();
          visitInstruction(*CS.getInstruction());
        } else {
          errs() << "Modelling " << I << " with an uninterpreted function\n";
          Expr name = mkTerm<const Function *>(f, m_efac);
          Expr d = bind::fdecl(name, sorts);
          Expr uf = bind::fapp(d, fargs);
          side(mk<EQ>(lhs, uf));
        }
      } else {
        if (m_fparams.size() > 3) {
          m_fparams.resize(3);
          errs() << "WARNING: skipping a call to " << F.getName()
                 << " (recursive call?)\n";
        }

        visitInstruction(*CS.getInstruction());
      }
    }
  }

  void visitAllocaInst(AllocaInst &I) {
    if (!m_sem.isTracked(I))
      return;

    Expr lhs = havoc(I);
    // -- alloca always returns a non-zero address
    side(mk<BUGT>(lhs, nullBv));
  }

  void visitLoadInst(LoadInst &I) {
    if (InferMemSafety2) {
      Value *pop = I.getPointerOperand()->stripPointerCasts();
      // -- successful load through a gep implies that the base
      // -- address of the gep is not null
      if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(pop)) {
        Expr base = lookup(*gep->getPointerOperand());
        if (base)
          side(mk<BUGT>(base, nullBv), true);
      }
    }

    if (!m_sem.isTracked(I))
      return;

    Expr lhs = havoc(I);
    if (!m_inMem)
      return;

    if (m_uniq) {
      Expr rhs = m_inMem;
      if (I.getType()->isIntegerTy(1))
        rhs = mk<NEQ>(rhs, falseBv);
      if (UseWrite2)
        write(I, rhs);
      else
        side(lhs, rhs);
    } else if (Expr op0 = lookup(*I.getPointerOperand())) {
      Expr rhs = op::array::select(m_inMem, op0);

      if (PartMem2) {
        side(mk<BULE>(m_s.read(m_cur_startMem), op0));
        side(mk<BULE>(mk<BADD>(op0, bv::bvnum(ptrSz(), ptrSz(), m_efac)),
                      m_s.read(m_cur_endMem)));

        side(mk<BULT>(op0, m_largestPtr));

        /// addresses must be aligned
        unsigned sz = I.getAlignment();
        addAlignConstraint(op0, sz);
      }

      if (I.getType()->isIntegerTy(1))
        rhs = mk<NEQ>(rhs, nullBv);
      else if (m_sem.sizeInBits(I) < ptrSz())
        rhs = bv::extract(m_sem.sizeInBits(I) - 1, 0, rhs);

      if (m_sem.sizeInBits(I) > ptrSz()) {
        errs() << "WARNING: fat integers not supported: "
               << "size " << m_sem.sizeInBits(I) << " > "
               << "pointer size " << ptrSz() << " in" << I << "\n"
               << "Ignored instruction.\n";
        return;
      }
      assert(m_sem.sizeInBits(I) <= ptrSz() && "Fat integers not supported");

      if (UseWrite2)
        write(I, rhs);
      else
        side(lhs, rhs);
    }

    m_inMem.reset();
  }

  void visitStoreInst(StoreInst &I) {
    if (InferMemSafety2) {
      Value *pop = I.getPointerOperand()->stripPointerCasts();
      // -- successful load through a gep implies that the base
      // -- address of the gep is not null
      if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(pop)) {
        Expr base = lookup(*gep->getPointerOperand());
        if (base)
          side(mk<BUGT>(base, nullBv), true);
      }
    }

    if (!m_inMem || !m_outMem || !m_sem.isTracked(*I.getOperand(0)))
      return;

    Expr v = lookup(*I.getOperand(0));

    if (v && I.getOperand(0)->getType()->isIntegerTy(1))
      v = boolToBv(v);

    if (m_uniq) {
      if (v)
        side(m_outMem, v);
    } else {
      if (m_sem.sizeInBits(*I.getOperand(0)) < ptrSz())
        v = bv::zext(v, ptrSz());

      if (m_sem.sizeInBits(*I.getOperand(0)) > ptrSz()) {
        errs() << "WARNING: fat pointers are not supported: "
               << "size " << m_sem.sizeInBits(*I.getOperand(0)) << " > "
               << "pointer size " << ptrSz() << " in" << I << "\n"
               << "Ignored instruction.\n";
        return;
      }

      assert(m_sem.sizeInBits(*I.getOperand(0)) <= ptrSz() &&
             "Fat pointers are not supported");

      Expr idx = lookup(*I.getPointerOperand());
      if (idx && v) {
        if (PartMem2) {
          side(mk<BULE>(m_s.read(m_cur_startMem), idx));
          side(mk<BULE>(mk<BADD>(idx, bv::bvnum(ptrSz(), ptrSz(), m_efac)),
                        m_s.read(m_cur_endMem)));

          side(mk<BULT>(idx, m_largestPtr));
          /// addresses must be aligned
          unsigned sz = I.getAlignment();
          addAlignConstraint(idx, sz);
        }
        side(m_outMem, op::array::store(m_inMem, idx, v));
      }
    }

    m_inMem.reset();
    m_outMem.reset();
  }

  void visitCastInst(CastInst &I) {
    if (!m_sem.isTracked(I))
      return;

    Expr lhs = havoc(I);
    const Value &v0 = *I.getOperand(0);
    Expr u = lookup(v0);

    // -- what can this be? Might need to do something here.
    if (UseWrite2)
      write(I, lookup(v0));
    else
      side(lhs, lookup(v0));
  }

  void initGlobals(const BasicBlock &BB) {
    const Function &F = *BB.getParent();
    if (&F.getEntryBlock() != &BB)
      return;
    if (!F.getName().equals("main"))
      return;

    const Module &M = *F.getParent();
    for (const GlobalVariable &g :
         boost::make_iterator_range(M.global_begin(), M.global_end())) {
      if (m_sem.isTracked(g)) {
        havoc(g);
        if (InferMemSafety2)
          // globals are non-null
          side(mk<BUGT>(lookup(g), nullBv));
      }
    }
  }

  void visitBasicBlock(BasicBlock &BB) {
    /// -- check if globals need to be initialized
    initGlobals(BB);

    // read the error flag to make it live
    m_s.read(m_sem.errorFlag(BB));
  }
};

struct OpSemPhiVisitor : public InstVisitor<OpSemPhiVisitor>, OpSemBase {
  const BasicBlock &m_dst;

  OpSemPhiVisitor(SymStore &s, Bv2OpSem &sem, ExprVector &side,
                  const BasicBlock &dst)
      : OpSemBase(s, sem, side), m_dst(dst) {}

  void visitBasicBlock(BasicBlock &BB) {
    // -- evaluate all phi-nodes atomically. First read all incoming
    // -- values, then update phi-nodes all together.
    ExprVector ops;

    auto curr = BB.begin();
    if (!isa<PHINode>(curr))
      return;

    for (; PHINode *phi = dyn_cast<PHINode>(curr); ++curr) {
      // skip phi nodes that are not tracked
      if (!m_sem.isTracked(*phi))
        continue;
      const Value &v = *phi->getIncomingValueForBlock(&m_dst);
      ops.push_back(lookup(v));
    }

    curr = BB.begin();
    for (unsigned i = 0; isa<PHINode>(curr); ++curr) {
      PHINode &phi = *cast<PHINode>(curr);
      if (!m_sem.isTracked(phi))
        continue;
      Expr lhs = havoc(phi);
      Expr op0 = ops[i++];
      if (UseWrite2)
        write(phi, op0);
      else
        side(lhs, op0);
    }
  }
};
} // namespace

namespace seahorn {
Expr Bv2OpSem::errorFlag(const BasicBlock &BB) {
  // -- if BB belongs to a function that cannot fail, errorFlag is always false
  if (m_canFail && !m_canFail->canFail(BB.getParent()))
    return falseE;
  return this->OpSem::errorFlag(BB);
}

Expr Bv2OpSem::memStart(unsigned id) {
  Expr sort = bv::bvsort(pointerSizeInBits(), m_efac);
  return shadow_dsa::memStartVar(id, sort);
}

Expr Bv2OpSem::memEnd(unsigned id) {
  Expr sort = bv::bvsort(pointerSizeInBits(), m_efac);
  return shadow_dsa::memEndVar(id, sort);
}

void Bv2OpSem::exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
                   Expr act) {
  OpSemContext C(s, side);
  C.update_bb(bb);
  C.m_act = act;

  // skip PHI instructions
  for (; isa<PHINode>(C.m_inst); ++C.m_inst) ;

  while (intraStep(C)) {
    /* do nothing */  ;
  }

  // OpSemVisitor v(s, *this, side);
  // v.setActiveLit(act);
  // v.visit(const_cast<BasicBlock &>(bb));
  // v.resetActiveLit();
}

void Bv2OpSem::exec(SymStore &s, const Instruction &inst, ExprVector &side) {
  OpSemContext C(s, side);
  C.update_bb(*(inst.getParent()));
  C.m_inst = BasicBlock::const_iterator(&inst);
  intraStep(C);
  // OpSemVisitor v(s, *this, side);
  // v.visit(const_cast<Instruction &>(inst));
}

void Bv2OpSem::execPhi(SymStore &s, const BasicBlock &bb, const BasicBlock &from,
                      ExprVector &side, Expr act) {
  /// TODO: all PHINodes must be executed together as a block.
  /// TODO: so need phiStep in addition to intraStep and intraBr

  // OpSemContext C(s, side);
  // C.update_bb(bb);
  // C.m_prev = &from;
  // C.m_act = act;
  // for (; isa<PHINode>(C.m_inst); ) {
  //   intraStep(C);
  // }

  // act is ignored since phi node only introduces a definition
  OpSemPhiVisitor v(s, *this, side, from);
  v.setActiveLit(act);
  v.visit(const_cast<BasicBlock &>(bb));
  v.resetActiveLit();
}

Expr Bv2OpSem::symbolicIndexedOffset(SymStore &s, GetElementPtrInst& gep) {
  unsigned ptrSz = pointerSizeInBits();

  // numeric offset
  uint64_t noffset = 0;
  // symbolic offset
  Expr soffset;

  for(auto TI = gep_type_begin(&gep), TE = gep_type_end(&gep); TI != TE; ++TI) {
    Value* CurVal = TI.getOperand();
    if (StructType *STy = TI.getStructTypeOrNull()) {
      unsigned fieldNo = cast<ConstantInt>(CurVal)->getZExtValue();
      noffset += fieldOff(STy, fieldNo);
    } else {
      assert(TI.isSequential());
      unsigned sz = storageSize(TI.getIndexedType());
      if (ConstantInt *ci = dyn_cast<ConstantInt>(CurVal)) {
        int64_t arrayIdx = ci->getSExtValue();
        noffset += (uint64_t)arrayIdx * sz;
      } else {
        Expr a = lookup(s, *CurVal);
        assert(a);
        a = mk<BMUL>(a, bv::bvnum(sz, ptrSz, m_efac));
	soffset = (soffset ? mk<BADD>(soffset, a): a);
      }
    }
  }

  Expr res;
  if (noffset > 0)
    res = bv::bvnum(/* cast to make clang on osx happy */
                    (unsigned long int)noffset, ptrSz, m_efac);
  if (soffset)
    res = res ? mk<BADD>(soffset, res) : soffset;

  if (!res) {
    assert(noffset == 0);
    assert(!soffset);
    res = bv::bvnum((unsigned long int)noffset, ptrSz, m_efac);
  }

  return res;
}

unsigned Bv2OpSem::pointerSizeInBits() const {
  return m_td->getPointerSizeInBits();
}

uint64_t Bv2OpSem::sizeInBits(const llvm::Type &t) const {
  return m_td->getTypeSizeInBits(const_cast<llvm::Type *>(&t));
}

uint64_t Bv2OpSem::sizeInBits(const llvm::Value &v) const {
  return sizeInBits(*v.getType());
}

unsigned Bv2OpSem::storageSize(const llvm::Type *t) const {
  return m_td->getTypeStoreSize(const_cast<Type *>(t));
}

unsigned Bv2OpSem::fieldOff(const StructType *t, unsigned field) const {
  return m_td->getStructLayout(const_cast<StructType *>(t))
      ->getElementOffset(field);
}

Expr Bv2OpSem::symb(const Value &I) {
  assert(!isa<UndefValue>(&I));

  // -- basic blocks are mapped to Bool constants
  if (const BasicBlock *bb = dyn_cast<const BasicBlock>(&I))
    return bind::boolConst(mkTerm<const BasicBlock *>(bb, m_efac));

  // -- constants are mapped to values
  if (const Constant *cv = dyn_cast<const Constant>(&I)) {
    if (const ConstantInt *c = dyn_cast<const ConstantInt>(&I)) {
      if (c->getType()->isIntegerTy(1))
        return c->isOne() ? mk<TRUE>(m_efac) : mk<FALSE>(m_efac);
      mpz_class k = toMpz(c->getValue());
      return bv::bvnum(k, sizeInBits(I), m_efac);
    } else if (cv->isNullValue() || isa<ConstantPointerNull>(&I))
      return bv::bvnum(0, sizeInBits(*cv), m_efac);
    else if (const ConstantExpr *ce = dyn_cast<const ConstantExpr>(&I)) {
      // XXX Need a better handling of constant expressions
      // XXX Perhaps fold using constant folding first, than evaluate the result
      // -- if this is a cast, and not into a Boolean, strip it
      if (ce->isCast() &&
          (ce->getType()->isIntegerTy() || ce->getType()->isPointerTy()) &&
          !ce->getType()->isIntegerTy(1))

      {
        if (const ConstantInt *val =
                dyn_cast<const ConstantInt>(ce->getOperand(0))) {
          mpz_class k = toMpz(val->getValue());
          return bv::bvnum(k, sizeInBits(I), m_efac);
        }
        // -- strip cast
        else
          return symb(*ce->getOperand(0));
      }
    }
  }

  // -- everything else is mapped to a constant
  Expr v = mkTerm<const Value *>(&I, m_efac);

  const Value *scalar = nullptr;
  if (isShadowMem(I, &scalar)) {
    if (scalar) {
      assert(scalar->getType()->isPointerTy());
      Type &eTy = *cast<PointerType>(scalar->getType())->getElementType();
      // -- create a constant with the name v[scalar]
      return bv::bvConst(
          op::array::select(v, mkTerm<const Value *>(scalar, m_efac)),
          sizeInBits(eTy));
    }

    if (m_trackLvl >= MEM) {
      Expr ptrTy = bv::bvsort(pointerSizeInBits(), m_efac);
      Expr valTy = ptrTy;
      Expr memTy = sort::arrayTy(ptrTy, valTy);
      return bind::mkConst(v, memTy);
    }
  }

  if (isTracked(I))
    return I.getType()->isIntegerTy(1) ? bind::boolConst(v)
                                       : bv::bvConst(v, sizeInBits(I));

  return Expr(0);
}

const Value &Bv2OpSem::conc(Expr v) {
  assert(isOpX<FAPP>(v));
  // name of the app
  Expr u = bind::fname(v);
  // name of the fdecl
  u = bind::fname(u);
  assert(isOpX<VALUE>(v));
  return *getTerm<const Value *>(v);
}

bool Bv2OpSem::isTracked(const Value &v) {
  const Value *scalar = nullptr;

  // -- shadow values represent memory regions
  // -- only track them when memory is tracked
  if (isShadowMem(v, &scalar))
    return scalar != nullptr || m_trackLvl >= MEM;

  // -- a pointer
  if (v.getType()->isPointerTy()) {
    // -- XXX A hack because shadow.mem generates not well formed
    // -- bitcode that contains future references. A register that
    // -- is defined later is used to name a shadow region in the
    // -- beginning of the function. Perhaps there is a better
    // -- solution. For now, we just do not track anything that came
    // -- that way.
    if (v.hasOneUse())
      if (const CallInst *ci = dyn_cast<const CallInst>(*v.user_begin()))
        if (const Function *fn = ci->getCalledFunction())
          if (fn->getName().startswith("shadow.mem"))
            return false;

    return m_trackLvl >= PTR;
  }

  // -- always track integer registers
  return v.getType()->isIntegerTy();
}

Expr Bv2OpSem::lookup(SymStore &s, const Value &v) {
  Expr u = symb(v);
  // if u is defined it is either an fapp or a constant
  if (u)
    return bind::isFapp(u) ? s.read(u) : u;
  return Expr(0);
}

void Bv2OpSem::execEdg(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                      ExprVector &side) {
  exec(s, src, side, trueE);
  execBr(s, src, dst, side, trueE);
  execPhi(s, dst, src, side, trueE);

  // an edge into a basic block that does not return includes the block itself
  const TerminatorInst *term = dst.getTerminator();
  if (term && isa<const UnreachableInst>(term))
    exec(s, dst, side, trueE);
}

void Bv2OpSem::execBr(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                     ExprVector &side, Expr act) {
  OpSemContext C(s, side);
  C.update_bb(src);
  C.m_inst = BasicBlock::const_iterator(src.getTerminator());
  C.m_act = act;
  intraBr(C, dst);
}

  /// \brief Executes one intra-procedural instructions in the current context
  /// Assumes that current instruction is not a branch
  bool Bv2OpSem::intraStep(OpSemContext &C) {
    if (C.m_inst == C.m_bb->end()) return false;
    if (isa<TerminatorInst> (C.m_inst)) return false;
    ++C.m_inst;
    /// XXX execute instruction
    return true;
  }

  /// \brief Executes one intra-procedural branch instruction in the
  /// current context. Assumes that current instruction is a branch
  void Bv2OpSem::intraBr(OpSemContext &C, const BasicBlock &dst) {
    const BranchInst *br = dyn_cast<const BranchInst>(C.m_inst);
    if (!br) return;

    // next instruction
    ++C.m_inst;

    if (br->isConditional()) {
      const Value &c = *br->getCondition();
      if (const Constant *cv = dyn_cast<const Constant>(&c)) {
        auto gv = getConstantValue(cv);
        assert(gv.hasValue());
        if (gv->IntVal.isOneValue() && br->getSuccessor(0) != &dst ||
            gv->IntVal.isNullValue() && br->getSuccessor(1) != &dst) {
          C.reset_side();
          C.add_side_safe(C.read(errorFlag(*C.m_bb)));
        }
      } else if (Expr target = lookup(C.m_values, c)) {
        Expr cond = br->getSuccessor(0) == &dst ? target : mk<NEG>(target);
        cond = boolop::lor(C.read(errorFlag(*C.m_bb)), cond);
        C.add_side_safe(cond);
        C.update_bb(dst);
      }
    }
    else {
      if (br->getSuccessor(0) != &dst) {
        C.reset_side();
        C.add_side_safe(C.read(errorFlag(*C.m_bb)));
      } else {
        C.update_bb(dst);
      }
    }
}

/// Adapted from llvm::ExecutionEngine
Optional<GenericValue> Bv2OpSem::getConstantValue(const Constant *C) {
  // If its undefined, return the garbage.
  if (isa<UndefValue>(C)) {
    GenericValue Result;
    switch (C->getType()->getTypeID()) {
    default:
      break;
    case Type::IntegerTyID:
    case Type::X86_FP80TyID:
    case Type::FP128TyID:
    case Type::PPC_FP128TyID:
      // Although the value is undefined, we still have to construct an APInt
      // with the correct bit width.
      Result.IntVal = APInt(C->getType()->getPrimitiveSizeInBits(), 0);
      break;
    case Type::StructTyID: {
      // if the whole struct is 'undef' just reserve memory for the value.
      if(StructType *STy = dyn_cast<StructType>(C->getType())) {
        unsigned int elemNum = STy->getNumElements();
        Result.AggregateVal.resize(elemNum);
        for (unsigned int i = 0; i < elemNum; ++i) {
          Type *ElemTy = STy->getElementType(i);
          if (ElemTy->isIntegerTy())
            Result.AggregateVal[i].IntVal =
              APInt(ElemTy->getPrimitiveSizeInBits(), 0);
          else if (ElemTy->isAggregateType()) {
            const Constant *ElemUndef = UndefValue::get(ElemTy);
            Result.AggregateVal[i] = getConstantValue(ElemUndef).getValue();
          }
        }
      }
    }
      break;
    case Type::VectorTyID:
      // if the whole vector is 'undef' just reserve memory for the value.
      auto* VTy = dyn_cast<VectorType>(C->getType());
      Type *ElemTy = VTy->getElementType();
      unsigned int elemNum = VTy->getNumElements();
      Result.AggregateVal.resize(elemNum);
      if (ElemTy->isIntegerTy())
        for (unsigned int i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].IntVal =
            APInt(ElemTy->getPrimitiveSizeInBits(), 0);
      break;
    }
    return Result;
  }

  // Otherwise, if the value is a ConstantExpr...
  if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
    Constant *Op0 = CE->getOperand(0);
    switch (CE->getOpcode()) {
    case Instruction::GetElementPtr: {
      // Compute the index
      GenericValue Result = getConstantValue(Op0).getValue();
      APInt Offset(m_td->getPointerSizeInBits(), 0);
      cast<GEPOperator>(CE)->accumulateConstantOffset(*m_td, Offset);

      char* tmp = (char*) Result.PointerVal;
      Result = PTOGV(tmp + Offset.getSExtValue());
      return Result;
    }
    case Instruction::Trunc: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.trunc(BitWidth);
      return GV;
    }
    case Instruction::ZExt: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.zext(BitWidth);
      return GV;
    }
    case Instruction::SExt: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.sext(BitWidth);
      return GV;
    }
    case Instruction::FPTrunc: {
      // FIXME long double
      GenericValue GV = getConstantValue(Op0).getValue();
      GV.FloatVal = float(GV.DoubleVal);
      return GV;
    }
    case Instruction::FPExt:{
      // FIXME long double
      GenericValue GV = getConstantValue(Op0).getValue();
      GV.DoubleVal = double(GV.FloatVal);
      return GV;
    }
    case Instruction::UIToFP: {
      GenericValue GV = getConstantValue(Op0).getValue();
      if (CE->getType()->isFloatTy())
        GV.FloatVal = float(GV.IntVal.roundToDouble());
      else if (CE->getType()->isDoubleTy())
        GV.DoubleVal = GV.IntVal.roundToDouble();
      else if (CE->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat::getZero(APFloat::x87DoubleExtended());
        (void)apf.convertFromAPInt(GV.IntVal,
                                   false,
                                   APFloat::rmNearestTiesToEven);
        GV.IntVal = apf.bitcastToAPInt();
      }
      return GV;
    }
    case Instruction::SIToFP: {
      GenericValue GV = getConstantValue(Op0).getValue();
      if (CE->getType()->isFloatTy())
        GV.FloatVal = float(GV.IntVal.signedRoundToDouble());
      else if (CE->getType()->isDoubleTy())
        GV.DoubleVal = GV.IntVal.signedRoundToDouble();
      else if (CE->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat::getZero(APFloat::x87DoubleExtended());
        (void)apf.convertFromAPInt(GV.IntVal,
                                   true,
                                   APFloat::rmNearestTiesToEven);
        GV.IntVal = apf.bitcastToAPInt();
      }
      return GV;
    }
    case Instruction::FPToUI: // double->APInt conversion handles sign
    case Instruction::FPToSI: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      if (Op0->getType()->isFloatTy())
        GV.IntVal = APIntOps::RoundFloatToAPInt(GV.FloatVal, BitWidth);
      else if (Op0->getType()->isDoubleTy())
        GV.IntVal = APIntOps::RoundDoubleToAPInt(GV.DoubleVal, BitWidth);
      else if (Op0->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat(APFloat::x87DoubleExtended(), GV.IntVal);
        uint64_t v;
        bool ignored;
        (void)apf.convertToInteger(makeMutableArrayRef(v), BitWidth,
                                   CE->getOpcode()==Instruction::FPToSI,
                                   APFloat::rmTowardZero, &ignored);
        GV.IntVal = v; // endian?
      }
      return GV;
    }
    case Instruction::PtrToInt: {
      auto OGV = getConstantValue(Op0);
      if (!OGV.hasValue()) return llvm::None;
      GenericValue GV = OGV.getValue();

      uint32_t PtrWidth = m_td->getTypeSizeInBits(Op0->getType());
      assert(PtrWidth <= 64 && "Bad pointer width");
      GV.IntVal = APInt(PtrWidth, uintptr_t(GV.PointerVal));
      uint32_t IntWidth = m_td->getTypeSizeInBits(CE->getType());
      GV.IntVal = GV.IntVal.zextOrTrunc(IntWidth);
      return GV;
    }
    case Instruction::IntToPtr: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t PtrWidth = m_td->getTypeSizeInBits(CE->getType());
      GV.IntVal = GV.IntVal.zextOrTrunc(PtrWidth);
      assert(GV.IntVal.getBitWidth() <= 64 && "Bad pointer width");
      GV.PointerVal = PointerTy(uintptr_t(GV.IntVal.getZExtValue()));
      return GV;
    }
    case Instruction::BitCast: {
      GenericValue GV = getConstantValue(Op0).getValue();
      Type* DestTy = CE->getType();
      switch (Op0->getType()->getTypeID()) {
      default: llvm_unreachable("Invalid bitcast operand");
      case Type::IntegerTyID:
        assert(DestTy->isFloatingPointTy() && "invalid bitcast");
        if (DestTy->isFloatTy())
          GV.FloatVal = GV.IntVal.bitsToFloat();
        else if (DestTy->isDoubleTy())
          GV.DoubleVal = GV.IntVal.bitsToDouble();
        break;
      case Type::FloatTyID:
        assert(DestTy->isIntegerTy(32) && "Invalid bitcast");
        GV.IntVal = APInt::floatToBits(GV.FloatVal);
        break;
      case Type::DoubleTyID:
        assert(DestTy->isIntegerTy(64) && "Invalid bitcast");
        GV.IntVal = APInt::doubleToBits(GV.DoubleVal);
        break;
      case Type::PointerTyID:
        assert(DestTy->isPointerTy() && "Invalid bitcast");
        break; // getConstantValue(Op0)  above already converted it
      }
      return GV;
    }
    case Instruction::Add:
    case Instruction::FAdd:
    case Instruction::Sub:
    case Instruction::FSub:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor: {
      GenericValue LHS = getConstantValue(Op0).getValue();
      GenericValue RHS = getConstantValue(CE->getOperand(1)).getValue();
      GenericValue GV;
      switch (CE->getOperand(0)->getType()->getTypeID()) {
      default: llvm_unreachable("Bad add type!");
      case Type::IntegerTyID:
        switch (CE->getOpcode()) {
        default: llvm_unreachable("Invalid integer opcode");
        case Instruction::Add: GV.IntVal = LHS.IntVal + RHS.IntVal; break;
        case Instruction::Sub: GV.IntVal = LHS.IntVal - RHS.IntVal; break;
        case Instruction::Mul: GV.IntVal = LHS.IntVal * RHS.IntVal; break;
        case Instruction::UDiv:GV.IntVal = LHS.IntVal.udiv(RHS.IntVal); break;
        case Instruction::SDiv:GV.IntVal = LHS.IntVal.sdiv(RHS.IntVal); break;
        case Instruction::URem:GV.IntVal = LHS.IntVal.urem(RHS.IntVal); break;
        case Instruction::SRem:GV.IntVal = LHS.IntVal.srem(RHS.IntVal); break;
        case Instruction::And: GV.IntVal = LHS.IntVal & RHS.IntVal; break;
        case Instruction::Or:  GV.IntVal = LHS.IntVal | RHS.IntVal; break;
        case Instruction::Xor: GV.IntVal = LHS.IntVal ^ RHS.IntVal; break;
        }
        break;
      case Type::FloatTyID:
        switch (CE->getOpcode()) {
        default: llvm_unreachable("Invalid float opcode");
        case Instruction::FAdd:
          GV.FloatVal = LHS.FloatVal + RHS.FloatVal; break;
        case Instruction::FSub:
          GV.FloatVal = LHS.FloatVal - RHS.FloatVal; break;
        case Instruction::FMul:
          GV.FloatVal = LHS.FloatVal * RHS.FloatVal; break;
        case Instruction::FDiv:
          GV.FloatVal = LHS.FloatVal / RHS.FloatVal; break;
        case Instruction::FRem:
          GV.FloatVal = std::fmod(LHS.FloatVal,RHS.FloatVal); break;
        }
        break;
      case Type::DoubleTyID:
        switch (CE->getOpcode()) {
        default: llvm_unreachable("Invalid double opcode");
        case Instruction::FAdd:
          GV.DoubleVal = LHS.DoubleVal + RHS.DoubleVal; break;
        case Instruction::FSub:
          GV.DoubleVal = LHS.DoubleVal - RHS.DoubleVal; break;
        case Instruction::FMul:
          GV.DoubleVal = LHS.DoubleVal * RHS.DoubleVal; break;
        case Instruction::FDiv:
          GV.DoubleVal = LHS.DoubleVal / RHS.DoubleVal; break;
        case Instruction::FRem:
          GV.DoubleVal = std::fmod(LHS.DoubleVal,RHS.DoubleVal); break;
        }
        break;
      case Type::X86_FP80TyID:
      case Type::PPC_FP128TyID:
      case Type::FP128TyID: {
        const fltSemantics &Sem = CE->getOperand(0)->getType()->getFltSemantics();
        APFloat apfLHS = APFloat(Sem, LHS.IntVal);
        switch (CE->getOpcode()) {
        default: llvm_unreachable("Invalid long double opcode");
        case Instruction::FAdd:
          apfLHS.add(APFloat(Sem, RHS.IntVal), APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FSub:
          apfLHS.subtract(APFloat(Sem, RHS.IntVal),
                          APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FMul:
          apfLHS.multiply(APFloat(Sem, RHS.IntVal),
                          APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FDiv:
          apfLHS.divide(APFloat(Sem, RHS.IntVal),
                        APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FRem:
          apfLHS.mod(APFloat(Sem, RHS.IntVal));
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        }
      }
        break;
      }
      return GV;
    }
    default:
      break;
    }

    SmallString<256> Msg;
    raw_svector_ostream OS(Msg);
    OS << "ConstantExpr not handled: " << *CE;
    report_fatal_error(OS.str());
  }

  // Otherwise, we have a simple constant.
  GenericValue Result;
  switch (C->getType()->getTypeID()) {
  case Type::FloatTyID:
    Result.FloatVal = cast<ConstantFP>(C)->getValueAPF().convertToFloat();
    break;
  case Type::DoubleTyID:
    Result.DoubleVal = cast<ConstantFP>(C)->getValueAPF().convertToDouble();
    break;
  case Type::X86_FP80TyID:
  case Type::FP128TyID:
  case Type::PPC_FP128TyID:
    Result.IntVal = cast <ConstantFP>(C)->getValueAPF().bitcastToAPInt();
    break;
  case Type::IntegerTyID:
    Result.IntVal = cast<ConstantInt>(C)->getValue();
    break;
  case Type::PointerTyID:
    if (isa<ConstantPointerNull>(C))
      Result.PointerVal = nullptr;
    else if (const Function *F = dyn_cast<Function>(C))
      /// XXX TODO
      //Result = PTOGV(getPointerToFunctionOrStub(const_cast<Function*>(F)));
      return llvm::None;
    else if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(C))
      // XXX TODO
      // Result = PTOGV(getOrEmitGlobalVariable(const_cast<GlobalVariable*>(GV)));
      return llvm::None;
    else
      llvm_unreachable("Unknown constant pointer type!");
    break;
  case Type::VectorTyID: {
    unsigned elemNum;
    Type* ElemTy;
    const ConstantDataVector *CDV = dyn_cast<ConstantDataVector>(C);
    const ConstantVector *CV = dyn_cast<ConstantVector>(C);
    const ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(C);

    if (CDV) {
      elemNum = CDV->getNumElements();
      ElemTy = CDV->getElementType();
    } else if (CV || CAZ) {
      VectorType* VTy = dyn_cast<VectorType>(C->getType());
      elemNum = VTy->getNumElements();
      ElemTy = VTy->getElementType();
    } else {
      llvm_unreachable("Unknown constant vector type!");
    }

    Result.AggregateVal.resize(elemNum);
    // Check if vector holds floats.
    if(ElemTy->isFloatTy()) {
      if (CAZ) {
        GenericValue floatZero;
        floatZero.FloatVal = 0.f;
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  floatZero);
        break;
      }
      if(CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].FloatVal = cast<ConstantFP>(
              CV->getOperand(i))->getValueAPF().convertToFloat();
        break;
      }
      if(CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].FloatVal = CDV->getElementAsFloat(i);

      break;
    }
    // Check if vector holds doubles.
    if (ElemTy->isDoubleTy()) {
      if (CAZ) {
        GenericValue doubleZero;
        doubleZero.DoubleVal = 0.0;
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  doubleZero);
        break;
      }
      if(CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].DoubleVal = cast<ConstantFP>(
              CV->getOperand(i))->getValueAPF().convertToDouble();
        break;
      }
      if(CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].DoubleVal = CDV->getElementAsDouble(i);

      break;
    }
    // Check if vector holds integers.
    if (ElemTy->isIntegerTy()) {
      if (CAZ) {
        GenericValue intZero;
        intZero.IntVal = APInt(ElemTy->getScalarSizeInBits(), 0ull);
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  intZero);
        break;
      }
      if(CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].IntVal = cast<ConstantInt>(
              CV->getOperand(i))->getValue();
          else {
            Result.AggregateVal[i].IntVal =
              APInt(CV->getOperand(i)->getType()->getPrimitiveSizeInBits(), 0);
          }
        break;
      }
      if(CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].IntVal = APInt(
            CDV->getElementType()->getPrimitiveSizeInBits(),
            CDV->getElementAsInteger(i));

      break;
    }
    llvm_unreachable("Unknown constant pointer type!");
  }
    break;

  default:
    SmallString<256> Msg;
    raw_svector_ostream OS(Msg);
    OS << "ERROR: Constant unimplemented for type: " << *C->getType();
    report_fatal_error(OS.str());
  }

  return Result;
}

} // namespace seahorn
