#include "llvm/IR/GetElementPtrTypeIterator.h"

#include "seahorn/BvOpSem2.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "ufo/ufo_iterators.hpp"
#include "llvm/Support/CommandLine.h"

using namespace seahorn;
using namespace llvm;
using namespace ufo;

using gep_type_iterator = generic_gep_type_iterator<>;

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

namespace seahorn {
namespace bvop_details {
struct OpSemBase {
  OpSemContext &m_ctx;
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

  OpSemBase(OpSemContext &ctx, Bv2OpSem &sem)
      : m_ctx(ctx), m_s(m_ctx.m_values), m_efac(m_ctx.getExprFactory()),
        m_sem(sem), m_side(m_ctx.m_side), m_cur_startMem(nullptr),
        m_cur_endMem(nullptr), m_largestPtr(nullptr) {

    trueE = m_sem.trueE;
    falseE = m_sem.falseE;
    zeroE = m_sem.zeroE;
    oneE = m_sem.oneE;
    trueBv = m_sem.trueBv;
    falseBv = m_sem.falseBv;
    nullBv = m_sem.nullBv;

    m_ctx.setMemScalar(false);
    m_ctx.m_act = trueE;

    m_largestPtr = m_sem.maxPtrE;

    // -- first two arguments are reserved for error flag,
    // -- the other is function activation
    ctx.pushParameter(falseE);
    ctx.pushParameter(falseE);
    ctx.pushParameter(falseE);
  }

  Expr symb(const Value &v) { return m_sem.symb(v); }
  unsigned ptrSz() { return m_sem.pointerSizeInBits(); }

  Expr read(const Value &v) {
    return m_sem.isSkipped(v) ? Expr(0) : m_ctx.read(symb(v));
  }

  Expr read(Expr v) { return m_ctx.read(v); }

  Expr lookup(const Value &v) { return m_sem.getOperandValue(v, m_ctx); }

  Expr havoc(const Value &v) {
    return m_sem.isSkipped(v) ? Expr(0) : m_ctx.m_values.havoc(symb(v));
  }

  void write(const Value &v, Expr val) {
    if (m_sem.isSkipped(v))
      return;
    m_s.write(symb(v), val);
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

  void setValue(const Value &v, Expr e) {
    Expr symReg = symb(v);
    assert(symReg);

    if (e) {
      m_ctx.m_values.write(symReg, e);
    } else {
      m_sem.unhandledValue(v, m_ctx);
      m_ctx.m_values.havoc(symReg);
    }
  }
};

struct OpSemVisitor : public InstVisitor<OpSemVisitor>, OpSemBase {
  OpSemVisitor(OpSemContext &ctx, Bv2OpSem &sem) : OpSemBase(ctx, sem) {}

  // Opcode Implementations
  void visitReturnInst(ReturnInst &I) {
    // -- skip return argument of main
    if (I.getParent()->getParent()->getName().equals("main"))
      return;

    // read the operand of return instruction so that the read is observable
    // b symstore
    if (I.getNumOperands() > 0)
      lookup(*I.getOperand(0));
  }
  void visitBranchInst(BranchInst &I) {
    if (I.isConditional())
      lookup(*I.getCondition());
  }

  void visitSwitchInst(SwitchInst &I) {
    llvm_unreachable("switch instructions are not supported. Must be lowered.");
  }
  void visitIndirectBrInst(IndirectBrInst &I) { llvm_unreachable(nullptr); }

  void visitBinaryOperator(BinaryOperator &I) {
    Type *ty = I.getOperand(0)->getType();
    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    if (op0 && op1) {
      switch (I.getOpcode()) {
      default:
        errs() << "Unknown binary operator: " << I << "\n";
        llvm_unreachable(nullptr);
        break;
      case Instruction::Add:
        res = mk<BADD>(op0, op1);
        break;
      case Instruction::Sub:
        res = mk<BSUB>(op0, op1);
        break;
      case Instruction::Mul:
        res = mk<BMUL>(op0, op1);
        break;
      case Instruction::FAdd:
        break;
      case Instruction::FSub:
        break;
      case Instruction::FMul:
        break;
      case Instruction::FDiv:
        break;
      case Instruction::FRem:
        break;
      case Instruction::UDiv:
        res = mk<BUDIV>(op0, op1);
        break;
      case Instruction::SDiv:
        res = mk<BSDIV>(op0, op1);
        break;
      case Instruction::URem:
        res = mk<BUREM>(op0, op1);
        break;
      case Instruction::SRem:
        res = mk<BSREM>(op0, op1);
        break;
      case Instruction::And:
        res = ty->isIntegerTy(1) ? mk<AND>(op0, op1) : mk<BAND>(op0, op1);
        break;
      case Instruction::Or:
        res = ty->isIntegerTy(1) ? mk<OR>(op0, op1) : mk<BOR>(op0, op1);
      case Instruction::Xor:
        res = ty->isIntegerTy(1) ? mk<XOR>(op0, op1) : mk<BXOR>(op0, op1);
      }
    }

    setValue(I, res);
  }

  void visitICmpInst(ICmpInst &I) {
    Type *ty = I.getOperand(0)->getType();
    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      switch (I.getPredicate()) {
      case ICmpInst::ICMP_EQ:
        res = executeICMP_EQ(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_NE:
        res = executeICMP_NE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_ULT:
        res = executeICMP_ULT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SLT:
        res = executeICMP_SLT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_UGT:
        res = executeICMP_UGT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SGT:
        res = executeICMP_SGT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_ULE:
        res = executeICMP_ULE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SLE:
        res = executeICMP_SLE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_UGE:
        res = executeICMP_UGE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SGE:
        res = executeICMP_SGE(op0, op1, ty, m_ctx);
        break;
      default:
        errs() << "Unknown ICMP predicate" << I;
        llvm_unreachable(nullptr);
      }
    }
    setValue(I, res);
  }

  void visitFCmpInst(FCmpInst &I) { llvm_unreachable(nullptr); }

  void visitAllocaInst_wip(AllocaInst &I) {
    Type *ty = I.getType()->getElementType();
    unsigned typeSz = (size_t)m_sem.m_td->getTypeAllocSize(ty);

    if (const Constant *cv = dyn_cast<const Constant>(I.getOperand(0))) {
      auto ogv = m_sem.getConstantValue(cv);
      if (!ogv.hasValue()) {
        llvm_unreachable(nullptr);
      }
      unsigned nElts = ogv.getValue().IntVal.getZExtValue();
      unsigned memSz = typeSz * nElts;
      LOG("opsem", errs() << "Alloca of " << memSz << " bytes: " << I << "\n";);
    } else {
      Expr nElts = lookup(*I.getOperand(0));
      LOG("opsem", errs() << "Alloca of " << nElts << "*" << typeSz
                          << " bytes: " << I << "\n";);
    }


    // allocate new address
    // XXX ignores allocation size
    Expr addr = havoc(I);

    // -- alloca always returns a non-zero address
    m_ctx.addSide(mk<BUGT>(addr, nullBv));
    setValue(I, addr);
  }

  void visitLoadInst(LoadInst &I) {
    setValue(I, executeLoadInst(*I.getPointerOperand(), I.getAlignment(),
                                I.getType(), m_ctx));
  }
  void visitStoreInst(StoreInst &I) {
    executeStoreInst(*I.getPointerOperand(), *I.getValueOperand(),
                     I.getAlignment(), m_ctx);
  }


  void visitGetElementPtrInst(GetElementPtrInst &I) {
    Expr val = executeGEPOperation(*I.getPointerOperand(),
                                   gep_type_begin(I), gep_type_end(I), m_ctx);
    setValue(I, val);
  }

  void visitPHINode(PHINode &PN) {
    llvm_unreachable("PHI nodes are handled by a different visitor!");
  }
  void visitTruncInst(TruncInst &I) {
    setValue(I, executeTruncInst(*I.getOperand(0), *I.getType(), m_ctx));
  }
  void visitZExtInst(ZExtInst &I) {
    setValue(I, executeZExtInst(*I.getOperand(0), *I.getType(), m_ctx));
  }
  void visitSExtInst(SExtInst &I) {
    setValue(I, executeSExtInst(*I.getOperand(0), *I.getType(), m_ctx));
  }

  // floating point instructions
  void visitFPTruncInst(FPTruncInst &I) { llvm_unreachable(nullptr); }
  void visitFPExtInst(FPExtInst &I) { llvm_unreachable(nullptr); }
  void visitUIToFPInst(UIToFPInst &I) { llvm_unreachable(nullptr); }
  void visitSIToFPInst(SIToFPInst &I) { llvm_unreachable(nullptr); }
  void visitFPToUIInst(FPToUIInst &I) { llvm_unreachable(nullptr); }
  void visitFPToSIInst(FPToSIInst &I) { llvm_unreachable(nullptr); }

  void visitPtrToIntInst(PtrToIntInst &I) {
    setValue(I, executePtrToIntInst(*I.getOperand(0), I.getType(), m_ctx));
  }
  void visitIntToPtrInst(IntToPtrInst &I) {
    setValue(I, executeIntToPtrInst(*I.getOperand(0), I.getType(), m_ctx));
  }

  void visitBitCastInst(BitCastInst &I) {
    setValue(I, executeBitCastInst(*I.getOperand(0), I.getType(), m_ctx));
  }

  void visitSelectInst(SelectInst &I) {
    Type *ty = I.getOperand(0)->getType();
    Expr cond = lookup(*I.getCondition());
    Expr op0 = lookup(*I.getTrueValue());
    Expr op1 = lookup(*I.getFalseValue());

    Expr res = executeSelectInst(cond, op0, op1, ty, m_ctx);
    setValue(I, res);
  }

  void visitCallSite(CallSite CS) {
    if (!CS.isCall()) {
      llvm_unreachable("invoke instructions "
                       "are not supported and must be lowered");
    }

    const Function *f = CS.getCalledFunction();
    if (!f) {
      visitIndirectCall(CS);
      return;
    }

    // -- should be handled by visitIntrinsicInst
    assert(!f->isIntrinsic());

    if (f->getName().startswith("verifier.assume")) {
      visitVerifierAssumeCall(CS);
      return;
    }

    if (f->getName().equals("calloc")) {
      visitCallocCall(CS);
      return;
    }

    if (f->getName().startswith("shadow.mem")) {
      visitShadowMemCall(CS);
      return;
    }

    if (f->isDeclaration()) {
      visitExternalCall(CS);
      return;
    }

    if (m_sem.hasFunctionInfo(*f)) {
      visitKnownFunctionCall(CS);
    }

    errs() << "Unhandled call instruction: " << *CS.getInstruction() << "\n";
    llvm_unreachable(nullptr);
  }

  void visitIndirectCall(CallSite CS) {
    // treat as non-det and issue a warning
    setValue(*CS.getInstruction(), Expr());
  }

  void visitVerifierAssumeCall(CallSite CS) {
    Function &f = *CS.getCalledFunction();

    Expr op = lookup(*CS.getArgument(0));
    if (f.getName().equals("verifier.assume.not"))
      op = boolop::lneg(op);

    if (!isOpX<TRUE>(op))
      m_ctx.addSideSafe(boolop::lor(
          m_ctx.read(m_sem.errorFlag(*(CS.getInstruction()->getParent()))),
          op));
  }

  void visitCallocCall(CallSite CS) {
    if (!m_ctx.getMemReadRegister() || !m_ctx.getMemReadRegister()) {
      LOG("opsem", errs() << "Warning: treating calloc() as nop\n";);
      return;
    }

    assert(!m_ctx.isMemScalar());

    if (IgnoreCalloc2) {
      LOG("opsem", "Warning: treating calloc() as malloc()\n";);
      m_ctx.addDef(read(m_ctx.getMemWriteRegister()),
                   read(m_ctx.getMemReadRegister()));
    } else {
      LOG("opsem", "Warning: allowing calloc() to "
                   "zero initialize ALL of its memory region\n";);
      m_ctx.addDef(m_ctx.read(m_ctx.getMemWriteRegister()),
                              op::array::constArray(bv::bvsort(ptrSz(), m_efac),
                                                    nullBv));
    }

    // get a fresh pointer
    const Instruction &inst = *CS.getInstruction();
    setValue(inst, havoc(inst));
  }

  void visitShadowMemCall(CallSite CS) {
    const Instruction &inst = *CS.getInstruction();

    const Function &F = *CS.getCalledFunction();
    if (F.getName().equals("shadow.mem.init")) {
      unsigned id = shadow_dsa::getShadowId(CS);
      assert(id >= 0);
      setValue(inst, havoc(inst));
      return;
    }

    if (F.getName().equals("shadow.mem.load")) {
      const Value &v = *CS.getArgument(1);
      m_ctx.setMemReadRegister(symb(v));
      m_ctx.setMemScalar(extractUniqueScalar(CS) != nullptr);
      return;
    }

    if (F.getName().equals("shadow.mem.store")) {
      Expr symReg = symb(inst);
      m_ctx.setMemReadRegister(symb(*CS.getArgument(1)));
      m_ctx.m_values.havoc(symReg);
      m_ctx.setMemWriteRegister(symReg);
      m_ctx.setMemScalar(extractUniqueScalar(CS) != nullptr);
      return;
    }

    if (F.getName().equals("shadow.mem.arg.ref")) {
      m_ctx.pushParameter(m_ctx.read(symb(*CS.getArgument(1))));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.mod")) {
      m_ctx.pushParameter(m_ctx.read(symb(*CS.getArgument(1))));
      m_ctx.pushParameter(m_ctx.m_values.havoc(symb(inst)));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.new")) {
      m_ctx.pushParameter(m_ctx.m_values.havoc(symb(inst)));
      return;
    }

    const Function &PF = *inst.getParent()->getParent();

    if (F.getName().equals("shadow.mem.in")) {
      if (PF.getName().equals("main"))
        setValue(inst, havoc(inst));
      else
        m_ctx.read(symb(*CS.getArgument(1)));
      return;
    }

    if (F.getName().equals("shadow.mem.out")) {
      if (PF.getName().equals("main"))
        setValue(inst, havoc(inst));
      else
        m_ctx.read(symb(*CS.getArgument(1)));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.init")) {
      if (PF.getName().equals("main"))
        setValue(inst, havoc(inst));
      return;
    }

    errs() << "Unknown shadow.mem call: " << inst << "\n";
    llvm_unreachable(nullptr);
  }

  void visitExternalCall(CallSite CS) {
    if (!EnableModelExternalCalls2)
      return;
    Function &F = *CS.getCalledFunction();
    if (F.getFunctionType()->getReturnType()->isVoidTy())
      return;

    if (std::find(IgnoreExternalFunctions2.begin(),
                  IgnoreExternalFunctions2.end(),
                  F.getName()) == IgnoreExternalFunctions2.end())
      return;

    const Instruction &inst = *CS.getInstruction();
    // Treat the call as an uninterpreted function
    Expr res;
    ExprVector fargs;
    ExprVector sorts;
    fargs.reserve(CS.arg_size());
    sorts.reserve(CS.arg_size());

    bool is_typed = true;
    for (auto &a : CS.args()) {
      if (m_sem.isSkipped(*a))
        continue;

      Expr e = lookup(*a);
      if (!e)
        continue;
      fargs.push_back(e);
      Expr s = bind::typeOf(e);
      if (!s) {
        // bind::typeOf is partially defined
        is_typed = false;
        break;
      }
      sorts.push_back(s);
    }

    if (is_typed) {
      // return type of the function
      Expr symReg = symb(inst);
      Expr ty = bind::typeOf(symReg);
      if (!ty) {
        is_typed = false;
      } else {
        sorts.push_back(ty);
      }
    }

    if (is_typed) {
      LOG("opsem", errs() << "Modelling " << inst
                          << " with an uninterpreted function\n";);
      Expr name = mkTerm<const Function *>(CS.getCalledFunction(), m_efac);
      Expr d = bind::fdecl(name, sorts);
      res = bind::fapp(d, fargs);
    }

    setValue(inst, res);
  }

  void visitKnownFunctionCall(CallSite CS) {
    const Function &F = *CS.getCalledFunction();
    const FunctionInfo &fi = m_sem.getFunctionInfo(F);
    const Instruction &inst = *CS.getInstruction();
    const BasicBlock &BB = *inst.getParent();

    // enabled
    m_ctx.setParameter(0, m_ctx.m_act); // activation literal
    // error flag in
    m_ctx.setParameter(1, m_ctx.read(m_sem.errorFlag(BB)));
    // error flag out
    m_ctx.setParameter(2, m_ctx.m_values.havoc(m_sem.errorFlag(BB)));
    for (const Argument *arg : fi.args)
      m_ctx.pushParameter(m_s.read(symb(*CS.getArgument(arg->getArgNo()))));
    for (const GlobalVariable *gv : fi.globals)
      m_ctx.pushParameter(m_s.read(symb(*gv)));

    if (fi.ret) {
      Expr v = m_ctx.m_values.havoc(symb(inst));
      setValue(inst, v);
      m_ctx.pushParameter(v);
    }

    LOG("arg_error", if (m_ctx.m_fparams.size() != bind::domainSz(fi.sumPred)) {
      const Instruction &I = *CS.getInstruction();
      const Function &PF = *BB.getParent();
      errs() << "Call instruction: " << I << "\n";
      errs() << "Caller: " << PF << "\n";
      errs() << "Callee: " << F << "\n";
      // errs () << "Sum predicate: " << *fi.sumPred << "\n";
      errs() << "m_ctx.m_fparams.size: " << m_ctx.m_fparams.size() << "\n";
      errs() << "Domain size: " << bind::domainSz(fi.sumPred) << "\n";
      errs() << "m_ctx.m_fparams\n";
      for (auto r : m_ctx.m_fparams)
        errs() << *r << "\n";
      errs() << "regions: " << fi.regions.size() << " args: " << fi.args.size()
             << " globals: " << fi.globals.size() << " ret: " << fi.ret << "\n";
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

    assert(m_ctx.m_fparams.size() == bind::domainSz(fi.sumPred));
    m_ctx.addSide(bind::fapp(fi.sumPred, m_ctx.getParameters()));

    m_ctx.resetParameters();
    m_ctx.pushParameter(falseE);
    m_ctx.pushParameter(falseE);
    m_ctx.pushParameter(falseE);
  }

  void visitIntrinsicInst(IntrinsicInst &I) {
    // interpret by non-determinism (and a warning)
    if (!I.getType()->isVoidTy())
      setValue(I, Expr());
  }

  void visitDbgDeclareInst(DbgDeclareInst &I) { /* nothing */
  }
  void visitDbgValueInst(DbgValueInst &I) { /* nothing */
  }
  void visitDbgInfoIntrinsic(DbgInfoIntrinsic &I) { /* nothing */
  }

  void visitMemSetInst(MemSetInst &I) {
    LOG("opsem", errs() << "Skipping memset: " << I << "\n";);
  }
  void visitMemCpyInst(MemCpyInst &I) {
    LOG("opsem", errs() << "Skipping memcpy: " << I << "\n";);
  }

  void visitMemMoveInst(MemMoveInst &I) {
    LOG("opsem", errs() << "Skipping memmove: " << I << "\n";);
  }
  void visitMemTransferInst(MemTransferInst &I) {
    LOG("opsem", errs() << "Unknown memtransfer: " << I << "\n";);
    llvm_unreachable(nullptr);
  }

  void visitMemIntrinsic(MemIntrinsic &I) {
    LOG("opsem", errs() << "Unknown memory intrinsic: " << I << "\n";);
    llvm_unreachable(nullptr);
  }

  void visitVAStartInst(VAStartInst &I) { llvm_unreachable(nullptr); }
  void visitVAEndInst(VAEndInst &I) { llvm_unreachable(nullptr); }
  void visitVACopyInst(VACopyInst &I) { llvm_unreachable(nullptr); }

  void visitUnreachableInst(UnreachableInst &I) { /* do nothing */
  }

  void visitShl(BinaryOperator &I) {
    Type *ty = I.getType();
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      res = mk<BSHL>(op0, op1);
    }

    setValue(I, res);
  }

  void visitLShr(BinaryOperator &I) {
    Type *ty = I.getType();
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      res = mk<BLSHR>(op0, op1);
    }

    setValue(I, res);
  }

  void visitAShr(BinaryOperator &I) {
    Type *ty = I.getType();
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      res = mk<BASHR>(op0, op1);
    }

    setValue(I, res);
  }

  void visitVAArgInst(VAArgInst &I) { llvm_unreachable(nullptr); }

  void visitExtractElementInst(ExtractElementInst &I) {
    llvm_unreachable(nullptr);
  }
  void visitInsertElementInst(InsertElementInst &I) {
    llvm_unreachable(nullptr);
  }
  void visitShuffleVectorInst(ShuffleVectorInst &I) {
    llvm_unreachable(nullptr);
  }

  // void visitExtractValueInst(ExtractValueInst &I);
  // void visitInsertValueInst(InsertValueInst &I);

  void visitInstruction(Instruction &I) {
    errs() << I << "\n";
    llvm_unreachable("No semantics to this instruction yet!");
  }

  Expr executeSelectInst(Expr cond, Expr op0, Expr op1, Type *ty,
                         OpSemContext &ctx) {
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }
    return cond && op0 && op1 ? mk<ITE>(cond, op0, op1) : Expr(0);
  }

  Expr executeTruncInst(const Value &v, const Type &ty, OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();

    uint64_t width = m_sem.sizeInBits(ty);
    Expr res = bv::extract(width - 1, 0, op0);
    return ty.isIntegerTy(1) ? bvToBool(res) : res;
  }

  Expr executeZExtInst(const Value &v, const Type &ty, OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();
    if (v.getType()->isIntegerTy(1))
      op0 = boolToBv(op0);
    return bv::zext(op0, m_sem.sizeInBits(ty));
  }

  Expr executeSExtInst(const Value &v, const Type &ty, OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();
    if (v.getType()->isIntegerTy(1))
      op0 = boolToBv(op0);
    return bv::sext(op0, m_sem.sizeInBits(ty));
  }

  Expr executeICMP_EQ(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<EQ>(op0, op1);
    case Type::PointerTyID:
      return mk<EQ>(op0, op1);
    default:
      errs() << "Unhandled ICMP_EQ predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_NE(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<NEQ>(op0, op1);
    case Type::PointerTyID:
      return mk<NEQ>(op0, op1);
    default:
      errs() << "Unhandled ICMP_NE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_ULT(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BULT>(op0, op1);
    case Type::PointerTyID:
      return mk<BULT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_ULT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SLT(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BSLT>(op0, op1);
    case Type::PointerTyID:
      return mk<BSLT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_UGT(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BUGT>(op0, op1);
    case Type::PointerTyID:
      return mk<BUGT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_UGT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SGT(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {

    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      if (ty->isIntegerTy(1)) {
        if (isOpX<TRUE>(op1))
          // icmp sgt op0, i1 true  == !op0
          return boolop::lneg(op0);
        else
          return bvToBool(mk<BSGT>(boolToBv(op0), boolToBv(op1)));
      }
      return mk<BSGT>(op0, op1);
    case Type::PointerTyID:
      return mk<BSGT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SGT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_ULE(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BULE>(op0, op1);
    case Type::PointerTyID:
      return mk<BULE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_ULE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SLE(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BSLE>(op0, op1);
    case Type::PointerTyID:
      return mk<BSLE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_UGE(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BUGE>(op0, op1);
    case Type::PointerTyID:
      return mk<BUGE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SGE(Expr op0, Expr op1, Type *ty, OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BSGE>(op0, op1);
    case Type::PointerTyID:
      return mk<BSGE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SGE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executePtrToIntInst(const Value &op, const Type *ty, OpSemContext &ctx) {
    Expr res = lookup(op);
    if (!res)
      return Expr();

    uint64_t dsz = m_sem.sizeInBits(*ty);
    uint64_t ssz = m_sem.sizeInBits(op);

    if (dsz > ssz)
      res = bv::zext(res, dsz);
    else if (dsz < ssz)
      res = bv::extract(dsz - 1, 0, res);

    return res;
  }

  Expr executeIntToPtrInst(const Value &op, const Type *ty, OpSemContext &ctx) {
    Expr res = lookup(op);
    if (!res)
      return Expr();

    uint64_t dsz = m_sem.sizeInBits(*ty);
    uint64_t ssz = m_sem.sizeInBits(op);

    if (dsz > ssz)
      res = bv::zext(res, dsz);
    else if (dsz < ssz)
      res = bv::extract(dsz - 1, 0, res);

    return res;
  }

  Expr executeGEPOperation(const Value &ptr,
                           gep_type_iterator it, gep_type_iterator end,
                           OpSemContext &ctx) {
    Expr res;
    Expr addr = lookup(ptr);
    Expr offset = m_sem.symbolicIndexedOffset(it, end, ctx);

    return addr && offset ? mk<BADD>(addr, offset) : Expr();
  }

  void visitAllocaInst(AllocaInst &I) {
    if (m_sem.isSkipped(I))
      return;

    Expr res = havoc(I);
    // -- alloca always returns a non-zero address
    m_ctx.addSide(mk<BUGT>(res, nullBv));
  }

  Expr executeLoadInst(const Value &addr, unsigned alignment, const Type *ty,
                       OpSemContext &ctx) {
    Expr res;
    if (!ctx.getMemReadRegister()) return res;

    if (ctx.isMemScalar()) {
      res = ctx.read(ctx.getMemReadRegister());
      if (ty->isIntegerTy(1))
        res = bvToBool(res);
    } else if (Expr op0 = lookup(addr)) {
      res = op::array::select(ctx.read(ctx.getMemReadRegister()), op0);
      if (ty->isIntegerTy(1))
        res = mk<NEQ>(res, nullBv);
      else if (m_sem.sizeInBits(*ty) < ptrSz())
        res = bv::extract(m_sem.sizeInBits(*ty) - 1, 0, res);

      if (m_sem.sizeInBits(*ty) > ptrSz()) {
        errs() << "WARNING: fat integers not supported: "
               << "size " << m_sem.sizeInBits(*ty) << " > "
               << "pointer size " << ptrSz() << " in load of" << addr << "\n"
               << "Ignored instruction.\n";
        llvm_unreachable(nullptr);
      }
      assert(m_sem.sizeInBits(*ty) <= ptrSz() && "Fat integers not supported");
    }

    ctx.setMemReadRegister(Expr());
    return res;
  }

  void executeStoreInst(const Value &addr, const Value &val, unsigned alignment,
                        OpSemContext &ctx) {

    if (!ctx.getMemReadRegister() || !ctx.getMemWriteRegister() ||
        m_sem.isSkipped(val)) {
      LOG("opsem",
          errs() << "Skipping store to " << addr << " of " << val << "\n";);
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return;
    }

    Expr v = lookup(val);

    if (v && val.getType()->isIntegerTy(1))
      v = boolToBv(v);

    if (ctx.isMemScalar()) {
      if (v)
        ctx.addDef(ctx.read(ctx.getMemWriteRegister()), v);
    } else {
      if (m_sem.sizeInBits(val) < ptrSz())
        v = bv::zext(v, ptrSz());

      if (m_sem.sizeInBits(val) > ptrSz()) {
        errs() << "WARNING: fat pointers are not supported: "
               << "size " << m_sem.sizeInBits(val) << " > "
               << "pointer size " << ptrSz() << " in store of " << val
               << " to addr " << addr << "\n";
        llvm_unreachable(nullptr);
      }

      assert(m_sem.sizeInBits(val) <= ptrSz() &&
             "Fat pointers are not supported");

      Expr idx = lookup(addr);
      if (idx && v) {
        ctx.addDef(ctx.read(ctx.getMemWriteRegister()),
                     op::array::store(ctx.read(ctx.getMemReadRegister()),
                                      idx, v));
      } else {
        LOG("opsem",
            errs() << "Skipping store to " << addr << " of " << val << "\n";);
      }
    }

    ctx.setMemReadRegister(Expr());
    ctx.setMemWriteRegister(Expr());
  }

  Expr executeBitCastInst(const Value &op, Type *ty, OpSemContext &ctx) {
    Type *opTy = op.getType();

    if (opTy->getTypeID() == Type::VectorTyID ||
        ty->getTypeID() == Type::VectorTyID)
      llvm_unreachable("Vector types are unsupported");

    Expr res = lookup(op);
    if (!res)
      return Expr();

    if (ty->isPointerTy())
      return res;

    if (ty->isIntegerTy()) {
      if (opTy->isFloatTy())
        llvm_unreachable("bitcast from float to int is not supported");
      else if (opTy->isDoubleTy())
        llvm_unreachable("bitcast from double to int is not supported");
      else if (opTy->isIntegerTy()) {
        return res;
      } else {
        llvm_unreachable("Invalid bitcast");
      }
    } else if (ty->isFloatTy()) {
      if (opTy->isIntegerTy())
        llvm_unreachable("bitcast to float not supported");
      else
        return res;
    } else if (ty->isDoubleTy()) {
      if (opTy->isIntegerTy())
        llvm_unreachable("bitcast to double not supported");
      else
        return res;
    }

    llvm_unreachable("Invalid bitcast");
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
      // TODO: skip globals that are not part of execution like @llvm.used
      if (!m_sem.isSkipped(g)) {
        havoc(g);
        if (InferMemSafety2)
          // globals are non-null
          m_ctx.addSide(mk<BUGT>(lookup(g), nullBv));
      }
    }
  }

  void visitBasicBlock(BasicBlock &BB) {
    /// -- check if globals need to be initialized
    initGlobals(BB);

    // read the error flag to make it live
    m_ctx.read(m_sem.errorFlag(BB));
  }
}; // namespace bvop_details

struct OpSemPhiVisitor : public InstVisitor<OpSemPhiVisitor>, OpSemBase {
  OpSemPhiVisitor(OpSemContext &ctx, Bv2OpSem &sem) : OpSemBase(ctx, sem) {}

  void visitBasicBlock(BasicBlock &BB) {
    // -- evaluate all phi-nodes atomically. First read all incoming
    // -- values, then update phi-nodes all together.
    llvm::SmallVector<Expr, 8> ops;

    auto curr = BB.begin();
    if (!isa<PHINode>(curr))
      return;

    // -- evaluate all incoming values in parallel
    for (; PHINode *phi = dyn_cast<PHINode>(curr); ++curr) {
      // skip phi nodes that are not tracked
      if (m_sem.isSkipped(*phi)) continue;
      const Value &v = *phi->getIncomingValueForBlock(m_ctx.m_prev);
      ops.push_back(lookup(v));
    }

    // -- set values to all PHINode registers
    curr = BB.begin();
    for (unsigned i = 0; PHINode *phi = dyn_cast<PHINode>(curr); ++curr) {
      if (m_sem.isSkipped(*phi)) continue;
      setValue(*phi, ops[i++]);
    }
  }
};
} // namespace bvop_details
} // namespace seahorn

namespace seahorn {
Bv2OpSem::Bv2OpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
                   TrackLevel trackLvl)
    : OpSem(efac), m_pass(pass), m_trackLvl(trackLvl), m_td(&dl) {
  m_canFail = pass.getAnalysisIfAvailable<CanFail>();

  trueE = mk<TRUE>(m_efac);
  falseE = mk<FALSE>(m_efac);

  zeroE = mkTerm<mpz_class>(0, m_efac);
  oneE = mkTerm<mpz_class>(1, m_efac);
  trueBv = bv::bvnum(1, 1, m_efac);
  falseBv = bv::bvnum(0, 1, m_efac);
  nullBv = bv::bvnum(0, pointerSizeInBits(), m_efac);

  mpz_class val;
  switch (pointerSizeInBits()) {
  case 64:
    // TODO: take alignment into account
    val = 0x000000000FFFFFFF;
    break;
  case 32:
    // TODO: take alignment into account
    val = 0x0FFFFFFF;
    break;
  default:
    LOG("opsem",
        errs() << "Unsupported pointer size: " << pointerSizeInBits() << "\n";);
    llvm_unreachable("Unexpected pointer size");
  }
  maxPtrE = bv::bvnum(val, pointerSizeInBits(), m_efac);
}

Bv2OpSem::Bv2OpSem(const Bv2OpSem &o)
    : OpSem(o), m_pass(o.m_pass), m_trackLvl(o.m_trackLvl), m_td(o.m_td),
      m_canFail(o.m_canFail), trueE(o.trueE), falseE(o.falseE), zeroE(o.zeroE),
      oneE(o.oneE), trueBv(o.trueBv), falseBv(o.falseBv), nullBv(o.nullBv) {}

Expr Bv2OpSem::errorFlag(const BasicBlock &BB) {
  // -- if BB belongs to a function that cannot fail, errorFlag is always false
  if (m_canFail && !m_canFail->canFail(BB.getParent()))
    return falseE;
  return this->OpSem::errorFlag(BB);
}

void Bv2OpSem::exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
                    Expr act) {
  OpSemContext C(s, side);
  C.update_bb(bb);
  C.m_act = act;

  // XXX this needs to be revised
  // do the setup necessary for a basic block
  bvop_details::OpSemVisitor v(C, *this);
  v.visitBasicBlock(const_cast<BasicBlock&>(bb));

  // skip PHI instructions
  for (; isa<PHINode>(C.m_inst); ++C.m_inst)
    ;

  while (intraStep(C)) {
    /* do nothing */;
  }
}

void Bv2OpSem::exec(SymStore &s, const Instruction &inst, ExprVector &side) {
  OpSemContext C(s, side);
  C.update_bb(*(inst.getParent()));
  C.m_inst = BasicBlock::const_iterator(&inst);
  intraStep(C);
  // OpSemVisitor v(s, *this, side);
  // v.visit(const_cast<Instruction &>(inst));
}

void Bv2OpSem::execPhi(SymStore &s, const BasicBlock &bb,
                       const BasicBlock &from, ExprVector &side, Expr act) {
  OpSemContext C(s, side);
  C.update_bb(bb);
  C.m_act = act;
  C.m_prev = &from;
  intraPhi(C);
}


Expr Bv2OpSem::symbolicIndexedOffset(gep_type_iterator TI, gep_type_iterator TE,
                                     OpSemContext &ctx) {
  unsigned ptrSz = pointerSizeInBits();

  // numeric offset
  uint64_t noffset = 0;
  // symbolic offset
  Expr soffset;

  for (; TI != TE; ++TI) {
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
        Expr a = getOperandValue(*CurVal, ctx);
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

Expr Bv2OpSem::getOperandValue(const Value &v, OpSemContext &ctx) {
  Expr symVal = symb(v);
  if (symVal)
    return isSymReg(symVal) ? ctx.read(symVal) : symVal;
  return Expr(0);
}

bool Bv2OpSem::isSymReg(Expr v) {
  if (this->OpSem::isSymReg(v)) return true;
  // TODO: memStart and memEnd

  // a symbolic register is any expression that resolves to an
  // llvm::Value XXX it might be better to register registers with a
  // SymStore and XXX let register be only expressions that are
  // explicitly marked as registers
  if (!isOpX<FAPP>(v)) return false;

  Expr u = bind::fname(v);
  u = bind::fname(u);
  if (isOpX<VALUE>(u)) return true;

  errs() << "Unexpected symbolic value: " << *v << "\n";
  llvm_unreachable(nullptr);
}

Expr Bv2OpSem::symb(const Value &I) {
  assert(!isa<UndefValue>(&I));

  // -- basic blocks are mapped to Bool constants
  if (const BasicBlock *bb = dyn_cast<const BasicBlock>(&I))
    return bind::boolConst(mkTerm<const BasicBlock *>(bb, m_efac));

  // -- constants are mapped to values
  if (const Constant *cv = dyn_cast<const Constant>(&I)) {
    // -- easy common cases
    if (cv->isNullValue() || isa<ConstantPointerNull>(&I))
      return bv::bvnum(0, sizeInBits(*cv), m_efac);
    else if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&I)) {
      if (ci->getType()->isIntegerTy(1))
        return ci->isOne() ? trueE : falseE;
      mpz_class k = toMpz(ci->getValue());
      return bv::bvnum(k, sizeInBits(I), m_efac);
    }

    if (cv->getType()->isIntegerTy()) {
      auto GVO = getConstantValue(cv);
      if (GVO.hasValue()) {
        GenericValue gv = GVO.getValue();
        mpz_class k = toMpz(gv.IntVal);
        if (cv->getType()->isIntegerTy(1)) {
          return k == 1 ? trueE : falseE;
        } else {
          return bv::bvnum(k, sizeInBits(I), m_efac);
        }
      }
    }

    LOG("opsem", errs() << "WARNING: Treating unsupported constant as non-det: "
                        << I << "\n";);
  }

  // everything else is mapped to a symbolic register with a
  // non-deterministic initial value
  Expr v = mkTerm<const Value *>(&I, m_efac);

  // pseudo register corresponding to memory blocks
  const Value *scalar = nullptr;
  if (isShadowMem(I, &scalar)) {
    // if memory is single cell, allocate regular register
    if (scalar) {
      assert(scalar->getType()->isPointerTy());
      Type &eTy = *cast<PointerType>(scalar->getType())->getElementType();
      // -- create a constant with the name v[scalar]
      return bv::bvConst(
          op::array::select(v, mkTerm<const Value *>(scalar, m_efac)),
          sizeInBits(eTy));
    }

    // if tracking memory content, create array-valued register for
    // the pseudo-assignment
    if (m_trackLvl >= MEM) {
      Expr ptrTy = bv::bvsort(pointerSizeInBits(), m_efac);
      Expr valTy = ptrTy;
      Expr memTy = sort::arrayTy(ptrTy, valTy);
      return bind::mkConst(v, memTy);
    }
  }

  // -- unexpected, return error to be handled elsewhere
  if (isSkipped(I))
    return Expr(0);

  const Type &ty = *I.getType();
  switch(ty.getTypeID()) {
  case Type::IntegerTyID:
    return ty.isIntegerTy(1) ? bind::boolConst(v)
      : bv::bvConst(v, sizeInBits(ty));
  case Type::PointerTyID:
    return bv::bvConst(v, sizeInBits(ty));
  default:
    errs() << "Error: unhandled type: " << ty << " of " << I << "\n";
    llvm_unreachable(nullptr);
  }
  llvm_unreachable(nullptr);
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

bool Bv2OpSem::isSkipped(const Value &v) {
  // skip shadow.mem instructions if memory is not a unique scalar
  // and we are now ignoring memory instructions
  const Value *scalar = nullptr;
  if (isShadowMem(v, &scalar)) {
    return scalar == nullptr && m_trackLvl < MEM;
  }

  const Type *ty = v.getType();
  if (ty->isPointerTy()) {
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
            return true;
    return m_trackLvl < PTR;
  }

  // -- explicitly name all types that we support
  // -- TODO: support arrays and struct values
  switch (ty->getTypeID()) {
  case Type::VoidTyID:
    return false;
  case Type::HalfTyID:
  case Type::FloatTyID:
  case Type::DoubleTyID:
  case Type::X86_FP80TyID:
  case Type::FP128TyID:
  case Type::PPC_FP128TyID:
    // floating types are not supported
    // TODO: integrate floating branch
    return true;
  case Type::LabelTyID:
    llvm_unreachable("Unexpected label type");
  case Type::MetadataTyID:
    llvm_unreachable("Unexpected metadata type");
  case Type::X86_MMXTyID:
    LOG("opsem", errs() << "Warning: Unsupported X86 type\n");
    return true;
  case Type::TokenTyID:
    llvm_unreachable("Unexpected token type");
  case Type::IntegerTyID:
    return false;
  case Type::FunctionTyID:
    llvm_unreachable("Unexpected function type");
  case Type::StructTyID:
    LOG("opsem", errs() << "Unsupported struct type\n";);
    return true;
  case Type::ArrayTyID:
    LOG("opsem", errs() << "Unsupported array type\n";);
    return true;
  case Type::PointerTyID:
    llvm_unreachable(nullptr);
  case Type::VectorTyID:
    LOG("opsem", errs() << "Unsupported vector type\n";);
    return true;
  default:
    LOG("opsem", errs() << "Unknown type: " << *ty << "\n";);
    llvm_unreachable(nullptr);
  }
  llvm_unreachable(nullptr);
}

void Bv2OpSem::execEdg(SymStore &s, const BasicBlock &src,
                       const BasicBlock &dst, ExprVector &side) {
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

/// \brief Executes one intra-procedural instructions in the current
/// context. Returns false if there are no more instructions to
/// execute after the last one
bool Bv2OpSem::intraStep(OpSemContext &C) {
  if (C.m_inst == C.m_bb->end())
    return false;

  const Instruction &inst = *(C.m_inst);

  // branch instructions must be executed to read the condition
  // on which the branch depends. This does not execute the branch
  // itself and does not advance instruction pointer in the context
  bool res = true;
  if (!isa<TerminatorInst>(C.m_inst)) {
    ++C.m_inst;
  } else if (isa<BranchInst>(C.m_inst)) {
    res = false;
  } else {
    return false;
  }

  // if instruction is skipped, execution it is a noop
  if (isSkipped(inst)) {
    skipInst(inst, C);
    return true;
  }

  bvop_details::OpSemVisitor v(C, *this);
  v.visit(const_cast<Instruction &>(inst));
  return res;
}

void Bv2OpSem::intraPhi(OpSemContext &C) {
  assert(C.m_prev);

  // XXX TODO: replace old code once regular semantics is ready

  // act is ignored since phi node only introduces a definition
  bvop_details::OpSemPhiVisitor v(C, *this);
  v.visitBasicBlock(const_cast<BasicBlock &>(*C.m_bb));
}
/// \brief Executes one intra-procedural branch instruction in the
/// current context. Assumes that current instruction is a branch
void Bv2OpSem::intraBr(OpSemContext &C, const BasicBlock &dst) {
  const BranchInst *br = dyn_cast<const BranchInst>(C.m_inst);
  if (!br)
    return;

  // next instruction
  ++C.m_inst;

  if (br->isConditional()) {
    const Value &c = *br->getCondition();
    if (const Constant *cv = dyn_cast<const Constant>(&c)) {
      auto gv = getConstantValue(cv);
      assert(gv.hasValue());
      if (gv->IntVal.isOneValue() && br->getSuccessor(0) != &dst ||
          gv->IntVal.isNullValue() && br->getSuccessor(1) != &dst) {
        C.resetSide();
        C.addSideSafe(C.read(errorFlag(*C.m_bb)));
      }
    } else if (Expr target = getOperandValue(c, C)) {
      Expr cond = br->getSuccessor(0) == &dst ? target : mk<NEG>(target);
      cond = boolop::lor(C.read(errorFlag(*C.m_bb)), cond);
      C.addSideSafe(cond);
      C.update_bb(dst);
    }
  } else {
    if (br->getSuccessor(0) != &dst) {
      C.resetSide();
      C.addSideSafe(C.read(errorFlag(*C.m_bb)));
    } else {
      C.update_bb(dst);
    }
  }
}

void Bv2OpSem::skipInst(const Instruction &inst, OpSemContext &ctx) {
  const Value *s;
  if (isShadowMem(inst, &s))
    return;
  if (ctx.m_ignored.count(&inst))
    return;
  ctx.m_ignored.insert(&inst);
  LOG("opsem", errs() << "WARNING: skipping instruction: " << inst << " @ "
                      << inst.getParent()->getName() << " in "
                      << inst.getParent()->getParent()->getName() << "\n");
}

void Bv2OpSem::unhandledValue(const Value &v, OpSemContext &ctx) {
  if (const Instruction *inst = dyn_cast<const Instruction>(&v))
    return unhandledInst(*inst, ctx);
  LOG("opsem", errs() << "WARNING: unhandled value: " << v << "\n";);
}
void Bv2OpSem::unhandledInst(const Instruction &inst, OpSemContext &ctx) {
  if (ctx.m_ignored.count(&inst))
    return;
  ctx.m_ignored.insert(&inst);
  LOG("opsem", errs() << "WARNING: unhadled instruction: " << inst << " @ "
                      << inst.getParent()->getName() << " in "
                      << inst.getParent()->getParent()->getName() << "\n");
}


Expr Bv2OpSem::memStart(unsigned id) {
  // TODO: reimplement
  Expr sort = bv::bvsort(pointerSizeInBits(), m_efac);
  return shadow_dsa::memStartVar(id, sort);
}

Expr Bv2OpSem::memEnd(unsigned id) {
  // TODO: reimplement
  Expr sort = bv::bvsort(pointerSizeInBits(), m_efac);
  return shadow_dsa::memEndVar(id, sort);
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
      if (StructType *STy = dyn_cast<StructType>(C->getType())) {
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
    } break;
    case Type::VectorTyID:
      // if the whole vector is 'undef' just reserve memory for the value.
      auto *VTy = dyn_cast<VectorType>(C->getType());
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

      char *tmp = (char *)Result.PointerVal;
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
    case Instruction::FPExt: {
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
        (void)apf.convertFromAPInt(GV.IntVal, false,
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
        (void)apf.convertFromAPInt(GV.IntVal, true,
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
                                   CE->getOpcode() == Instruction::FPToSI,
                                   APFloat::rmTowardZero, &ignored);
        GV.IntVal = v; // endian?
      }
      return GV;
    }
    case Instruction::PtrToInt: {
      auto OGV = getConstantValue(Op0);
      if (!OGV.hasValue())
        return llvm::None;
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
      Type *DestTy = CE->getType();
      switch (Op0->getType()->getTypeID()) {
      default:
        llvm_unreachable("Invalid bitcast operand");
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
      default:
        llvm_unreachable("Bad add type!");
      case Type::IntegerTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid integer opcode");
        case Instruction::Add:
          GV.IntVal = LHS.IntVal + RHS.IntVal;
          break;
        case Instruction::Sub:
          GV.IntVal = LHS.IntVal - RHS.IntVal;
          break;
        case Instruction::Mul:
          GV.IntVal = LHS.IntVal * RHS.IntVal;
          break;
        case Instruction::UDiv:
          GV.IntVal = LHS.IntVal.udiv(RHS.IntVal);
          break;
        case Instruction::SDiv:
          GV.IntVal = LHS.IntVal.sdiv(RHS.IntVal);
          break;
        case Instruction::URem:
          GV.IntVal = LHS.IntVal.urem(RHS.IntVal);
          break;
        case Instruction::SRem:
          GV.IntVal = LHS.IntVal.srem(RHS.IntVal);
          break;
        case Instruction::And:
          GV.IntVal = LHS.IntVal & RHS.IntVal;
          break;
        case Instruction::Or:
          GV.IntVal = LHS.IntVal | RHS.IntVal;
          break;
        case Instruction::Xor:
          GV.IntVal = LHS.IntVal ^ RHS.IntVal;
          break;
        }
        break;
      case Type::FloatTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid float opcode");
        case Instruction::FAdd:
          GV.FloatVal = LHS.FloatVal + RHS.FloatVal;
          break;
        case Instruction::FSub:
          GV.FloatVal = LHS.FloatVal - RHS.FloatVal;
          break;
        case Instruction::FMul:
          GV.FloatVal = LHS.FloatVal * RHS.FloatVal;
          break;
        case Instruction::FDiv:
          GV.FloatVal = LHS.FloatVal / RHS.FloatVal;
          break;
        case Instruction::FRem:
          GV.FloatVal = std::fmod(LHS.FloatVal, RHS.FloatVal);
          break;
        }
        break;
      case Type::DoubleTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid double opcode");
        case Instruction::FAdd:
          GV.DoubleVal = LHS.DoubleVal + RHS.DoubleVal;
          break;
        case Instruction::FSub:
          GV.DoubleVal = LHS.DoubleVal - RHS.DoubleVal;
          break;
        case Instruction::FMul:
          GV.DoubleVal = LHS.DoubleVal * RHS.DoubleVal;
          break;
        case Instruction::FDiv:
          GV.DoubleVal = LHS.DoubleVal / RHS.DoubleVal;
          break;
        case Instruction::FRem:
          GV.DoubleVal = std::fmod(LHS.DoubleVal, RHS.DoubleVal);
          break;
        }
        break;
      case Type::X86_FP80TyID:
      case Type::PPC_FP128TyID:
      case Type::FP128TyID: {
        const fltSemantics &Sem =
            CE->getOperand(0)->getType()->getFltSemantics();
        APFloat apfLHS = APFloat(Sem, LHS.IntVal);
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid long double opcode");
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
          apfLHS.divide(APFloat(Sem, RHS.IntVal), APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FRem:
          apfLHS.mod(APFloat(Sem, RHS.IntVal));
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        }
      } break;
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
    Result.IntVal = cast<ConstantFP>(C)->getValueAPF().bitcastToAPInt();
    break;
  case Type::IntegerTyID:
    Result.IntVal = cast<ConstantInt>(C)->getValue();
    break;
  case Type::PointerTyID:
    if (isa<ConstantPointerNull>(C))
      Result.PointerVal = nullptr;
    else if (const Function *F = dyn_cast<Function>(C))
      /// XXX TODO
      // Result = PTOGV(getPointerToFunctionOrStub(const_cast<Function*>(F)));
      return llvm::None;
    else if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(C))
      // XXX TODO
      // Result =
      // PTOGV(getOrEmitGlobalVariable(const_cast<GlobalVariable*>(GV)));
      return llvm::None;
    else
      llvm_unreachable("Unknown constant pointer type!");
    break;
  case Type::VectorTyID: {
    unsigned elemNum;
    Type *ElemTy;
    const ConstantDataVector *CDV = dyn_cast<ConstantDataVector>(C);
    const ConstantVector *CV = dyn_cast<ConstantVector>(C);
    const ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(C);

    if (CDV) {
      elemNum = CDV->getNumElements();
      ElemTy = CDV->getElementType();
    } else if (CV || CAZ) {
      VectorType *VTy = dyn_cast<VectorType>(C->getType());
      elemNum = VTy->getNumElements();
      ElemTy = VTy->getElementType();
    } else {
      llvm_unreachable("Unknown constant vector type!");
    }

    Result.AggregateVal.resize(elemNum);
    // Check if vector holds floats.
    if (ElemTy->isFloatTy()) {
      if (CAZ) {
        GenericValue floatZero;
        floatZero.FloatVal = 0.f;
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  floatZero);
        break;
      }
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].FloatVal =
                cast<ConstantFP>(CV->getOperand(i))
                    ->getValueAPF()
                    .convertToFloat();
        break;
      }
      if (CDV)
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
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].DoubleVal =
                cast<ConstantFP>(CV->getOperand(i))
                    ->getValueAPF()
                    .convertToDouble();
        break;
      }
      if (CDV)
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
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].IntVal =
                cast<ConstantInt>(CV->getOperand(i))->getValue();
          else {
            Result.AggregateVal[i].IntVal = APInt(
                CV->getOperand(i)->getType()->getPrimitiveSizeInBits(), 0);
          }
        break;
      }
      if (CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].IntVal =
              APInt(CDV->getElementType()->getPrimitiveSizeInBits(),
                    CDV->getElementAsInteger(i));

      break;
    }
    llvm_unreachable("Unknown constant pointer type!");
  } break;

  default:
    SmallString<256> Msg;
    raw_svector_ostream OS(Msg);
    OS << "ERROR: Constant unimplemented for type: " << *C->getType();
    report_fatal_error(OS.str());
  }

  return Result;
}

} // namespace seahorn
