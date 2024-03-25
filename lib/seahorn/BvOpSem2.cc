#include "seahorn/BvOpSem2.hh"
#include "BvOpSem2ExtraWideMemMgr.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/CodeGen/IntrinsicLowering.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/Regex.h"

#include "seahorn/CallUtils.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"

#include "BvOpSem2Context.hh"

#include "clam/ClamQueryAPI.hh"
#include "clam/SeaDsaHeapAbstraction.hh"
#include "crab/domains/abstract_domain_params.hpp"
#include "seahorn/clam_CfgBuilder.hh"
#include "seahorn/clam_Clam.hh"

#include "seadsa/ShadowMem.hh"

#include <fstream>
#include <memory>

using namespace llvm;
using namespace seahorn;
using namespace seahorn::details;
using gep_type_iterator = generic_gep_type_iterator<>;

namespace seahorn {
extern bool isUnifiedAssume(const Instruction &CI);
extern clam::CrabDomain::Type CrabDom;
namespace details {
enum class VacCheckOptions { NONE, ANTE, ALL };
}
} // namespace seahorn

static const llvm::Regex
    fatptr_intrnsc_re("^__sea_([A-Za-z]|_)*(extptr|recover).*");

static llvm::cl::opt<bool>
    UseLambdas("horn-bv2-lambdas",
               llvm::cl::desc("Use lambdas for array operations"),
               cl::init(false));

static llvm::cl::opt<bool> UseFatMemory(
    "horn-bv2-fatmem",
    llvm::cl::desc(
        "Use fat-memory model with fat pointers and fat memory locations"),
    cl::init(false));

static llvm::cl::opt<bool> UseWideMemory(
    "horn-bv2-widemem",
    llvm::cl::desc("Use wide-memory model with pointer and object size"),
    cl::init(false));

static llvm::cl::opt<bool> UseExtraWideMemory(
    "horn-bv2-extra-widemem",
    llvm::cl::desc(
        "Use extra wide memory model with base, offset and object size"),
    cl::init(false));

static llvm::cl::opt<bool> UseTrackingMemory(
    "horn-bv2-tracking-mem",
    llvm::cl::desc("Use Memory which stores metadata about Def and Use"),
    cl::init(false));

static llvm::cl::opt<unsigned>
    WordSize("horn-bv2-word-size",
             llvm::cl::desc("Word size in bytes: 0 - auto, 1, 4, 8"),
             cl::init(0));

static llvm::cl::opt<unsigned>
    PtrSize("horn-bv2-ptr-size",
            llvm::cl::desc("Pointer size in bytes: 0 - auto, 4, 8"),
            cl::init(0), cl::Hidden);

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

static llvm::cl::opt<bool> SimplifyExpr(
    "horn-bv2-simplify",
    llvm::cl::desc("Simplify expressions as they are written to memory"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    SimplifyExprNonMem("horn-bv2-simplify-nonmem",
                       llvm::cl::desc("Simplify non memory expressions"),
                       llvm::cl::init(true));

static llvm::cl::opt<enum seahorn::details::VacCheckOptions> VacuityCheckOpt(
    "horn-bv2-vacuity-check",
    llvm::cl::desc("A choice for levels of vacuity check"),
    llvm::cl::values(clEnumValN(seahorn::details::VacCheckOptions::NONE, "none",
                                "Don't perform any check"),
                     clEnumValN(seahorn::details::VacCheckOptions::ANTE,
                                "antecedent",
                                "Only perform check for antecedent"),
                     clEnumValN(seahorn::details::VacCheckOptions::ALL, "all",
                                "Perform check for antecedent and consequent")),
    llvm::cl::init(seahorn::details::VacCheckOptions::NONE));

static llvm::cl::opt<bool> UseIncVacSat(
    "horn-bv2-vacuity-check-inc",
    llvm::cl::desc(
        "Use incremental solver to check for vacuity and assertions"),
    llvm::cl::init(false));

static llvm::cl::opt<unsigned>
    MaxSizeGlobalVarInit("horn-bv2-max-gv-init-size",
                         llvm::cl::desc("Maximum size for global initializers"),
                         llvm::cl::init(0));

static llvm::cl::opt<bool>
    UseCrabInferRng("horn-bv2-crab-rng",
                    llvm::cl::desc("Use crab to infer rng invariants"),
                    llvm::cl::init(false));

// Crab does not understand sea.is_dereferenceable but the intrinsics
// is lowered into instructions that Crab can understand.
static llvm::cl::opt<bool> UseCrabLowerIsDeref(
    "horn-bv2-crab-lower-is-deref",
    llvm::cl::desc("Use crab to lower sea.is_dereferenceable"),
    llvm::cl::init(false));

// Crab reason natively about sea.is_dereferenceable without any
// lowering.
static llvm::cl::opt<bool> UseCrabCheckIsDeref(
    "horn-bv2-crab-check-is-deref",
    llvm::cl::desc("Use crab to check sea.is_dereferenceable"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> UseLVIInferRng(
    "horn-bv2-lvi-rng",
    llvm::cl::desc("Use LVI (LazyValueInfo) to infer rng invariants"),
    llvm::cl::init(false));
namespace {

const Value *extractUniqueScalar(const CallBase &CB) {
  if (!EnableUniqueScalars2)
    return nullptr;
  else
    return shadow_dsa::extractUniqueScalar(CB);
}

bool isShadowMem(const Value &V, const Value **out) {
  const Value *scalar;
  bool res = shadow_dsa::isShadowMem(V, &scalar);
  if (EnableUniqueScalars2 && out)
    *out = scalar;
  return res;
}

const seahorn::details::Bv2OpSemContext &const_ctx(const OpSemContext &_ctx);
} // namespace
namespace seahorn {

namespace details {
struct OpSemVisitorBase {
  Bv2OpSemContext &m_ctx;
  ExprFactory &m_efac;
  Bv2OpSem &m_sem;

  Expr trueE;
  Expr falseE;
  Expr zeroE;
  Expr oneE;

  OpSemVisitorBase(Bv2OpSemContext &ctx, Bv2OpSem &sem)
      : m_ctx(ctx), m_efac(m_ctx.getExprFactory()), m_sem(sem) {

    trueE = m_ctx.m_trueE;
    falseE = m_ctx.m_falseE;
    zeroE = m_ctx.zeroE;
    oneE = m_ctx.oneE;

    // XXX AG: this is probably wrong since instances of OpSemVisitorBase are
    // created
    // XXX AG: for each instruction, not just once per function
    // XXX AG: but not an issue at this point since function calls are not
    // handled by the semantics
    // -- first two arguments are reserved for error flag,
    // -- the other is function activation
    // ctx.pushParameter(falseE);
    // ctx.pushParameter(falseE);
    // ctx.pushParameter(falseE);
  }

  unsigned ptrSzInBits() { return m_ctx.ptrSzInBits(); }

  Expr read(const Value &v) {
    if (m_sem.isSkipped(v))
      return Expr();

    Expr reg;
    if ((reg = m_ctx.getRegister(v)))
      return m_ctx.read(reg);

    if (const Constant *cv = dyn_cast<Constant>(&v)) {
      return m_ctx.getConstantValue(*cv);
    }

    reg = m_ctx.mkRegister(v);
    if (reg)
      return m_ctx.read(reg);

    errs() << "Error: failed to read a value for: " << v << "\n";
    llvm_unreachable(nullptr);
  }

  Expr lookup(const Value &v) { return m_sem.getOperandValue(v, m_ctx); }

  /// \brief Havocs the register corresponding to \p v.
  ///
  /// Creates a register for \p v if necessary. Writes a new fresh symbolic
  /// constant to the store for \p v.
  ///
  /// \return the fresh value that was written or null (empty Expr).
  Expr havoc(const Value &v) {
    if (m_sem.isSkipped(v))
      return Expr();

    OpSemMemManager &memManager = m_ctx.mem();

    Expr reg;
    if ((reg = m_ctx.getRegister(v))) {
      Expr sort = bind::rangeTy(bind::fname(reg));
      Expr h = memManager.coerce(sort, m_ctx.havoc(reg));
      m_ctx.write(reg, h);
      return h;
    }

    if ((reg = m_ctx.mkRegister(v))) {
      Expr sort = bind::rangeTy(bind::fname(reg));
      Expr h = memManager.coerce(sort, m_ctx.havoc(reg));
      m_ctx.write(reg, h);
      return h;
    }

    errs() << "Error: failed to havoc: " << v << "\n";
    llvm_unreachable(nullptr);
  }

  void write(const Value &v, Expr val) {
    if (m_sem.isSkipped(v))
      return;

    Expr reg;
    if ((reg = m_ctx.getRegister(v)))
      m_ctx.write(reg, val);
    else {
      assert(!isa<Constant>(v));
      reg = m_ctx.mkRegister(v);
      if (reg)
        m_ctx.write(reg, val);
      else {
        errs() << "Error: failed to write: " << v << "\n";
        llvm_unreachable(nullptr);
      }
    }
  }

  void setValue(const Value &v, Expr e) {
    if (e)
      write(v, e);
    else {
      m_sem.unhandledValue(v, m_ctx);
      havoc(v);
    }
  }
};

static bool
clobbersFlagRegisters(const llvm::SmallVector<llvm::StringRef, 4> &AsmPieces) {

  if (AsmPieces.size() == 3 || AsmPieces.size() == 4) {
    if (std::count(AsmPieces.begin(), AsmPieces.end(), "~{cc}") &&
        std::count(AsmPieces.begin(), AsmPieces.end(), "~{flags}") &&
        std::count(AsmPieces.begin(), AsmPieces.end(), "~{fpsr}")) {

      if (AsmPieces.size() == 3)
        return true;
      else if (std::count(AsmPieces.begin(), AsmPieces.end(), "~{dirflag}"))
        return true;
    }
  }
  return false;
}

class OpSemVisitor : public InstVisitor<OpSemVisitor>, OpSemVisitorBase {
public:
  OpSemVisitor(Bv2OpSemContext &ctx, Bv2OpSem &sem)
      : OpSemVisitorBase(ctx, sem) {}

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
        res = m_ctx.alu().doAdd(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::Sub:
        res = m_ctx.alu().doSub(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::Mul:
        res = m_ctx.alu().doMul(op0, op1, ty->getScalarSizeInBits());
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
        res = m_ctx.alu().doUDiv(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::SDiv:
        res = m_ctx.alu().doSDiv(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::URem:
        res = m_ctx.alu().doURem(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::SRem:
        res = m_ctx.alu().doSRem(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::And:
        res = m_ctx.alu().doAnd(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::Or:
        res = m_ctx.alu().doOr(op0, op1, ty->getScalarSizeInBits());
        break;
      case Instruction::Xor:
        res = m_ctx.alu().doXor(op0, op1, ty->getScalarSizeInBits());
        break;
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

  void visitAllocaInst(AllocaInst &I) {
    Type *ty = I.getType()->getElementType();
    unsigned typeSz = (size_t)m_sem.getTD().getTypeAllocSize(ty);

    Expr addr;
    if (const Constant *cv = dyn_cast<const Constant>(I.getOperand(0))) {
      ConstantExprEvaluator ce(m_sem.getDataLayout());
      auto ogv = ce.evaluate(cv);
      if (!ogv.hasValue()) {
        llvm_unreachable(nullptr);
      }
      unsigned nElts = ogv.getValue().IntVal.getZExtValue();
      unsigned memSz = typeSz * nElts;
      LOG("opsem",
          errs() << "!3 Alloca of " << memSz << " bytes: " << I << "\n";);
      addr = m_ctx.mem().salloc(memSz);
    } else {
      Expr nElts = lookup(*I.getOperand(0));
      if (dagSize(nElts) < 64) {
        LOG("opsem", errs() << "!4 Alloca of (" << *nElts << " * " << typeSz
                            << ") bytes: " << I << "\n";);
      } else {
        LOG("opsem", errs() << "!4 Alloca of ...\n";);
      }
      addr = m_ctx.mem().salloc(nElts, typeSz);
    }

    setValue(I, addr);

    if (!m_ctx.getMemReadRegister() || !m_ctx.getMemWriteRegister()) {
      LOG("opsem",
          ERR << "No read/write register found - check if corresponding"
                 " shadow instruction is present.");
      m_ctx.setMemReadRegister(Expr());
      m_ctx.setMemWriteRegister(Expr());
      return;
    }

    // TODO: check that addr is valid
    auto memIn = m_ctx.read(m_ctx.getMemReadRegister());
    OpSemMemManager &memManager = m_ctx.mem();
    auto res = memManager.setMetadata(
        MetadataKind::ALLOC, addr, memIn,
        m_ctx.alu().num(1, memManager.getMetadataMemWordSzInBits()));
    m_ctx.write(m_ctx.getMemWriteRegister(), res);

    m_ctx.setMemReadRegister(Expr());
    m_ctx.setMemWriteRegister(Expr());
  }

  void visitLoadInst(LoadInst &I) {
    setValue(I, executeLoadInst(*I.getPointerOperand(), I.getAlignment(),
                                I.getType(), m_ctx));
  }
  void visitStoreInst(StoreInst &I) {
    executeStoreInst(*I.getValueOperand(), *I.getPointerOperand(),
                     I.getAlignment(), m_ctx);
  }

  void visitGetElementPtrInst(GetElementPtrInst &I) {
    Expr val = executeGEPOperation(*I.getPointerOperand(), gep_type_begin(I),
                                   gep_type_end(I), m_ctx);
    setValue(I, val);
  }

  void visitPHINode(PHINode &PN) {
    // -- there is a special visitor for PHINodes
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

  void visitCallBase(CallBase &CB) {
    if (!isa<CallInst>(CB)) {
      llvm_unreachable("invoke instructions "
                       "are not supported and must be lowered");
    }

    if (CB.isInlineAsm()) {
      visitInlineAsmCall(CB);
      return;
    }

    auto *f = getCalledFunction(CB);
    if (!f) {
      visitIndirectCall(CB);
      return;
    }

    // -- should be handled by visitIntrinsicInst
    assert(!f->isIntrinsic());

    if (f->getName().startswith("verifier.assume")) {
      visitVerifierAssumeCall(CB);
      return;
    }

    if (f->getName().equals("calloc")) {
      visitCallocCall(CB);
      return;
    }

    if (f->getFunctionType()->getReturnType()->isVoidTy()) {
      if (f->getName().startswith("_ZN4core3ptr56drop_in_place")) {
        // core::ptr::drop_in_place is recursive
        WARN << "Skipping a non-inlineable call to: " << f->getName();
        return;
      } else if (f->getName().find("core..clone..Clone$GT$5clone") !=
                 StringRef::npos) {
        // some implementations of ::clone are recursive
        // if we see a call, then it could not have been inlined, hence it is
        // recursive
        WARN << "Skipping a non-inlineable call to: " << f->getName();
        return;
      }
    }

    if (CB.getMetadata("shadow.mem")) {
      visitShadowMemCall(CB);
      return;
    }

    if (f->getName().startswith("shadow.mem")) {
      WARN << "missing metadata on shadow.mem functions. "
              "Probably using old ShadowMem pass. "
              "Some features might not work as expected";
      visitShadowMemCall(CB);
      return;
    }

    auto funDeclStartsWithVisitorMap = hana::make_map(
        hana::make_pair(BOOST_HANA_STRING("sea.is_dereferenceable"),
                        &OpSemVisitor::visitIsDereferenceable),
        hana::make_pair(BOOST_HANA_STRING("sea.is_modified"),
                        &OpSemVisitor::visitIsModified),
        hana::make_pair(BOOST_HANA_STRING("sea.reset_modified"),
                        &OpSemVisitor::visitResetModified),
        hana::make_pair(BOOST_HANA_STRING("sea.is_read"),
                        &OpSemVisitor::visitIsRead),
        hana::make_pair(BOOST_HANA_STRING("sea.reset_read"),
                        &OpSemVisitor::visitResetRead),
        hana::make_pair(BOOST_HANA_STRING("sea.is_alloc"),
                        &OpSemVisitor::visitIsAlloc),
        hana::make_pair(BOOST_HANA_STRING("sea.tracking_on"),
                        &OpSemVisitor::visitSetTrackingOn),
        hana::make_pair(BOOST_HANA_STRING("sea.tracking_off"),
                        &OpSemVisitor::visitSetTrackingOff),
        hana::make_pair(BOOST_HANA_STRING("sea.free"),
                        &OpSemVisitor::visitFree),
        hana::make_pair(BOOST_HANA_STRING("sea.assert.if"),
                        &OpSemVisitor::visitSeaAssertIfCall),
        hana::make_pair(BOOST_HANA_STRING("verifier.assert"),
                        &OpSemVisitor::visitVerifierAssertCall),
        hana::make_pair(BOOST_HANA_STRING("sea.branch_sentinel"),
                        &OpSemVisitor::visitBranchSentinel),
        hana::make_pair(BOOST_HANA_STRING("smt."), &OpSemVisitor::visitSmtCall),
        hana::make_pair(BOOST_HANA_STRING("sea.set_shadowmem"),
                        &OpSemVisitor::visitSetShadowMem),
        hana::make_pair(BOOST_HANA_STRING("sea.get_shadowmem"),
                        &OpSemVisitor::visitGetShadowMem));

    auto visitFunDecl = [&](StringRef candidate) {
      auto found = false;
      // Note: not efficient to loop through all keys.
      // There is no way to break a hana::for_each loop
      // The ease of adding a new instrinsic outweighs the cost of looping --
      // since the number of entries is small and not likely to grow 2x
      hana::for_each(hana::keys(funDeclStartsWithVisitorMap), [&](auto key) {
        if (candidate.startswith(key.c_str()) && !found) {
          auto fnPtr = funDeclStartsWithVisitorMap[key];
          (this->*fnPtr)(CB);
          found = true;
          return;
        }
      });
      return found;
    };

    if (f->isDeclaration()) {
      if (f->arg_empty() && (f->getName().startswith("nd") ||
                             f->getName().startswith("nondet.") ||
                             f->getName().endswith("nondet") ||
                             f->getName().startswith("verifier.nondet") ||
                             f->getName().startswith("__VERIFIER_nondet")))
        visitNondetCall(CB);
      else if (visitFunDecl(f->getName())) {
        return;
      } else if (fatptr_intrnsc_re.match(f->getName())) {
        visitFatPointerInstr(CB);
      } else
        visitExternalCall(CB);
      return;
    }

    if (m_sem.hasFunctionInfo(*f)) {
      visitKnownFunctionCall(CB);
    }

    ERR << "Unexpected call instruction: " << CB;
    ERR << "Either inlining failed, or calling a recursive function. "
           "Aborting...";
    assert(false);
    std::exit(1);
  }

  void visitSmtCall(CallBase &CB) {

    auto *f = getCalledFunction(CB);
    Expr res;
    if (f->getName().startswith("smt.extract.")) {
      auto *arg0 = dyn_cast<ConstantInt>(CB.getOperand(0));
      auto *arg1 = dyn_cast<ConstantInt>(CB.getOperand(1));
      auto *val = CB.getOperand(2);
      Expr symVal = lookup(*val);
      if (symVal && arg0 && arg1) {
        res =
            m_ctx.alu().Extract({symVal, val->getType()->getScalarSizeInBits()},
                                arg0->getZExtValue(), arg1->getZExtValue());
      }
    } else if (f->getName().startswith("smt.concat.")) {
      LOG("opsem", WARN << "Not implemented yet";);
      assert(false);
    } else {
      LOG("opsem", ERR << "Unsupported smt. function: " << f->getName(););
      assert(false);
    }

    setValue(CB, res);
  }

  void visitInlineAsmCall(CallBase &CB) {
    // We only care about handling simple cases e.g. which are used to
    // thwart optimization by obfuscating code.
    // Inline assembly format:
    // a string contains instructions, a list of operand constraints, (flags,
    // e.g. sideeffect) Specifically, we ONLY handle the following kinds of
    // inline assembly: 1) %_57 = call i64 asm sideeffect "",
    // "=r,0,~{dirflag},~{fpsr},~{flags}"(i64 %_14) #7, !dbg !504, !srcloc !505
    // @ _55 in main
    // 2) call void asm sideeffect "",
    // "r,~{memory},~{dirflag},~{fpsr},~{flags}"(i8* %7) #5, !dbg !102, !srcloc
    // !103
    // 3) Single instruction of bswap asm

    IntegerType *Ty = dyn_cast<IntegerType>(CB.getType());
    if ((Ty && Ty->getBitWidth() % 16 != 0) || CB.arg_size() > 1) {
      LOG("opsem", ERR << "Cannot handle inline assembly: " << CB);
      return;
    }
    InlineAsm *IA = cast<InlineAsm>(CB.getCalledOperand());
    const std::string &AsmStr = IA->getAsmString();
    llvm::SmallVector<llvm::StringRef, 4> AsmPieces;
    llvm::SplitString(AsmStr, AsmPieces, ";\n");
    switch (AsmPieces.size()) {
    default:
      LOG("opsem", ERR << "Cannot handle inline assembly: " << CB);
      break;
    case 0:
      // This part handles the following type of inline assembly
      // The other switch cases are handling integer bswap only
      // 1. read memory value (data), the type of value is not restricted
      if (IA->getConstraintString().compare(0, 5, "=r,0,") == 0) {
        // Copy input to output
        Expr readVal = lookup(*CB.getOperand(0));
        setValue(CB, readVal);
      } else if (IA->getConstraintString().compare(0, 2, "r,") == 0) {
        // This code is only used to stop optimization
        // Since there is no computation, do nothing
      } else {
        LOG("opsem",
            ERR << "Cannot handle inline assembly with empty asm string: "
                << CB);
      }
      break;
    case 1:
      bool isAsmHandled = false;
      // bswap
      if (AsmStr.compare(0, 8, "bswap $0") == 0 ||
          AsmStr.compare(0, 9, "bswapl $0") == 0 ||
          AsmStr.compare(0, 9, "bswapq $0") == 0 ||
          AsmStr.compare(0, 12, "bswap ${0:q}") == 0 ||
          AsmStr.compare(0, 13, "bswapl ${0:q}") == 0 ||
          AsmStr.compare(0, 13, "bswapq ${0:q}") == 0) {
        // No need to check constraints
        isAsmHandled = expandCallInst(cast<CallInst>(CB), [](CallInst &CI) {
          return IntrinsicLowering::LowerToByteSwap(&CI);
        });
      }
      // llvm.bswap.i16
      else if (CB.getType()->isIntegerTy(16) &&
               IA->getConstraintString().compare(0, 5, "=r,0,") == 0 &&
               (AsmStr.compare(0, 16, "rorw $$8, ${0:w}") == 0 ||
                AsmStr.compare(0, 16, "rolw $$8, ${0:w}") == 0)) {
        // Check Flag resgisters
        AsmPieces.clear();
        llvm::SplitString(StringRef(IA->getConstraintString()).substr(5),
                          AsmPieces, ",");
        // Try to replace a call instruction with a call to a bswap intrinsic
        isAsmHandled = clobbersFlagRegisters(AsmPieces) &&
                       expandCallInst(cast<CallInst>(CB), [](CallInst &CI) {
                         return IntrinsicLowering::LowerToByteSwap(&CI);
                       });
      }
      if (!isAsmHandled)
        LOG("opsem",
            ERR << "Cannot handle inline assembly of integer swap: " << CB);
      break;
    }
  }

  void visitBranchSentinel(CallBase &CB) {}

  void visitGetShadowMem(CallBase &CB) {
    if (!m_ctx.getMemReadRegister()) {
      LOG("opsem", ERR << "No read register found - check if corresponding"
                          "shadow instruction is present.");
      m_ctx.setMemReadRegister(Expr());
      return;
    }
    Expr slot = lookup(*CB.getOperand(0));
    if (!m_ctx.alu().isNum(slot)) {
      LOG("opsem", ERR << "Metadata slot should resolve to a number.");
      assert(false);
    }
    size_t slotNum = m_ctx.alu().toNum(slot).get_ui();
    if (slotNum >= m_ctx.mem().getNumOfMetadataSlots()) {
      LOG("opsem", ERR << "Metadata slot exceeds number of available slots.");
      assert(false);
    }
    Expr ptr = lookup(*CB.getOperand(1));
    auto memIn = m_ctx.read(m_ctx.getMemReadRegister());
    OpSemMemManager &memManager = m_ctx.mem();
    auto res =
        memManager.getMetadata(static_cast<MetadataKind>(slotNum), ptr, memIn,
                               memManager.getMetadataMemWordSzInBits() / 8);
    setValue(CB, res);
    m_ctx.setMemReadRegister(Expr());
  };

  void visitSetShadowMem(CallBase &CB) {
    Expr slot = lookup(*CB.getOperand(0));
    if (!m_ctx.alu().isNum(slot)) {
      LOG("opsem", ERR << "Metadata slot should resolve to a number.");
      assert(false);
    }
    size_t slotNum = m_ctx.alu().toNum(slot).get_ui();
    if (slotNum >= m_ctx.mem().getNumOfMetadataSlots()) {
      LOG("opsem", ERR << "Metadata slot exceeds number of available slots.");
      assert(false);
    }
    Expr ptr = lookup(*CB.getOperand(1));
    Expr exprToSet = lookup(*CB.getOperand(2));
    auto memIn = m_ctx.read(m_ctx.getMemReadRegister());
    Expr res = m_ctx.mem().setMetadata(static_cast<MetadataKind>(slotNum), ptr,
                                       memIn, exprToSet);
    m_ctx.write(m_ctx.getMemWriteRegister(), res);
    // clear hidden mem reg for next instruction
    m_ctx.setMemReadRegister(Expr());
    m_ctx.setMemWriteRegister(Expr());
  };

  void visitIsDereferenceable(CallBase &CB) {
    Expr ptr = lookup(*CB.getOperand(0));
    Expr byteSz = lookup(*CB.getOperand(1));
    Expr res;
    bool crabSolved = false;
    if (UseCrabLowerIsDeref || UseCrabCheckIsDeref) {
      // if crab is used, infer the result of sea.is_deref
      auto derefInfoFromCrab = m_sem.getCrabInstRng(CB);
      if (derefInfoFromCrab.isEmptySet()) {
        // Crab skips is_deref due to invariant inferred along the path is
        // bottom
        Stats::count("crab.isderef.solve");
        // Remove this is_deref checks
        res = m_ctx.alu().getTrue();
      } else if (derefInfoFromCrab.isSingleElement()) {
        // Crab inferred is_deref call is either true or false
        // Set the value for res expression
        Stats::count("crab.isderef.solve");
        res = derefInfoFromCrab.getSingleElement()->getBoolValue()
                  ? m_ctx.alu().getTrue()
                  : m_ctx.alu().getFalse();
        crabSolved = true;
      } else {
        Stats::count("crab.isderef.not.solve");
        LOG("opsem-crab", const llvm::DebugLoc &dloc = CB.getDebugLoc();
            unsigned Line = dloc.getLine(); unsigned Col = dloc.getCol();
            StringRef File = (*dloc).getFilename();
            MSG << "crab cannot solve: " << CB << " at File=" << File
                << " Line=" << Line << " col=" << Col;);
      }
    }
    if (!crabSolved) {
      res = m_ctx.mem().isDereferenceable(ptr, byteSz);
    }
    setValue(CB, res);
  }

  void visitIsModified(CallBase &CB) {
    if (!m_ctx.getMemReadRegister()) {
      LOG("opsem", ERR << "No read register found - check if corresponding"
                          "shadow instruction is present.");
      m_ctx.setMemReadRegister(Expr());
      return;
    }
    Expr ptr = lookup(*CB.getOperand(0));
    auto memIn = m_ctx.read(m_ctx.getMemReadRegister());
    OpSemMemManager &memManager = m_ctx.mem();
    auto res = memManager.isMetadataSet(MetadataKind::WRITE, ptr, memIn);
    setValue(CB, res);
    m_ctx.setMemReadRegister(Expr());
  }

  void visitResetModified(CallBase &CB) {
    if (!m_ctx.getMemReadRegister() || !m_ctx.getMemWriteRegister()) {
      LOG("opsem",
          ERR << "No read/write register found - check if corresponding"
                 "shadow instruction is present.");
      m_ctx.setMemReadRegister(Expr());
      m_ctx.setMemWriteRegister(Expr());
      return;
    }
    Expr ptr = lookup(*CB.getOperand(0));
    auto memIn = m_ctx.read(m_ctx.getMemReadRegister());
    OpSemMemManager &memManager = m_ctx.mem();
    auto res = memManager.setMetadata(
        MetadataKind::WRITE, ptr, memIn,
        m_ctx.alu().num(0, memManager.getMetadataMemWordSzInBits()));
    m_ctx.write(m_ctx.getMemWriteRegister(), res);

    m_ctx.setMemReadRegister(Expr());
    m_ctx.setMemWriteRegister(Expr());
  }

  void visitIsRead(CallBase &CB) {}

  void visitResetRead(CallBase &CB) {}

  void visitIsAlloc(CallBase &CB) {
    if (!m_ctx.getMemReadRegister()) {
      LOG("opsem", ERR << "No read register found - check if corresponding"
                          "shadow instruction is present.");
      m_ctx.setMemReadRegister(Expr());
      return;
    }
    Expr ptr = lookup(*CB.getOperand(0));
    auto memIn = m_ctx.read(m_ctx.getMemReadRegister());
    OpSemMemManager &memManager = m_ctx.mem();
    auto res = memManager.isMetadataSet(MetadataKind::ALLOC, ptr, memIn);
    setValue(CB, res);
    m_ctx.setMemReadRegister(Expr());
  }

  void visitSetTrackingOn(CallBase &CB) { m_ctx.setTracking(true); }

  void visitSetTrackingOff(CallBase &CB) { m_ctx.setTracking(false); }

  void visitFree(CallBase &CB) {
    if (!m_ctx.getMemReadRegister() || !m_ctx.getMemWriteRegister()) {
      LOG("opsem",
          ERR << "No read/write register found - check if corresponding"
                 "shadow instruction is present.");
      m_ctx.setMemReadRegister(Expr());
      m_ctx.setMemWriteRegister(Expr());
      return;
    }
    Expr ptr = lookup(*CB.getOperand(0));
    auto memIn = m_ctx.read(m_ctx.getMemReadRegister());
    OpSemMemManager &memManager = m_ctx.mem();
    auto res = memManager.setMetadata(
        MetadataKind::ALLOC, ptr, memIn,
        m_ctx.alu().num(0, memManager.getMetadataMemWordSzInBits()));
    m_ctx.write(m_ctx.getMemWriteRegister(), res);

    m_ctx.setMemReadRegister(Expr());
    m_ctx.setMemWriteRegister(Expr());
  }

  /// Report outcome of vacuity and incremental assertion checking
  void reportDoAssert(const char *tag, const Instruction &I, boost::tribool res,
                      bool expected) {

    bool isGood = false;

    if (res) {
      isGood = expected == true;
    } else if (!res) {
      isGood = expected == false;
    } else {
      isGood = false;
    }
    llvm::SmallString<256> msg;
    llvm::raw_svector_ostream out(msg);
    out << tag;
    out << (isGood ? " passed " : " failed ");

    out << "(" << (res ? "sat" : (!res ? "unsat" : "unknown")) << ") ";

    auto dloc = I.getDebugLoc();
    if (dloc) {
      out << dloc->getFilename() << ":" << dloc->getLine() << "]";
    } else {
      out << I;
    }

    if (I.hasMetadata("backedge_assert")) {
      out << " backedge!!";
    }

    (isGood ? INFO : ERR) << out.str();
  }

  void doAssert(Expr ante, Expr conseq, const Instruction &I) {
    ScopedStats __stats__("opsem.assert");
    if (VacuityCheckOpt == VacCheckOptions::NONE) {
      return;
    }
    // const llvm::DebugLoc &dloc = I.getDebugLoc();
    bool isBackEdge = I.hasMetadata("backedge_assert");
    Stats::resume("opsem.vacuity");
    // The solving is done incrementally. We only
    // reset the solver once per assert instruction.
    // We then add expressions incrementally.
    // This works because this check never needs to
    // remove an expression from the solver.
    boost::tribool anteRes = true;
    if (!isBackEdge)
      // -- skip vacuity check for instrumented assertions
      anteRes = solveWithConstraints(ante);

    Stats::stop("opsem.vacuity");
    // if ante is unsat then report false and bail out
    if (anteRes) {
      if (!isBackEdge) {
        reportDoAssert("vacuity", I, anteRes, true);
      }
    } else {
      reportDoAssert("vacuity", I, anteRes, true);
      return; // return early since conseq is unreachable
    }

    if (VacuityCheckOpt == VacCheckOptions::ANTE) {
      return; // don't need to process conseq
    }

    Expr nconseq = boolop::lneg(conseq);
    if (!UseIncVacSat) {
      nconseq = boolop::land(ante, nconseq);
    }

    Stats::resume("opsem.incbmc");
    auto conseqRes = solveWithConstraints(
        nconseq, !isBackEdge && UseIncVacSat /* incremental */);
    Stats::stop("opsem.incbmc");
    reportDoAssert("assertion", I, conseqRes, false);
  }

  void visitSeaAssertIfCall(CallBase &CB) {
    // NOTE: sea.assert.if.not is not supported
    Expr ante = lookup(*CB.getOperand(0));
    Expr conseq = lookup(*CB.getOperand(1));
    doAssert(ante, conseq, CB);
  }

  boost::tribool solveWithConstraints(const Expr &solveFor,
                                      bool incremental = false) const {
    // if incremental is true then use existing constraints in solver
    // else reset solver
    if (!incremental) {
      m_ctx.resetSolver();
    }
    for (auto e : m_ctx.side()) {
      m_ctx.addToSolver(e);
    }
    m_ctx.addToSolver(m_ctx.getPathCond());
    m_ctx.addToSolver(solveFor);

    auto r = m_ctx.solve();
    // if the solver returns unknown then dump smt2 formula to file for analysis
    LOG("opsem.dump.incassert", {
      if (r || !r) {
      } else { // indeterminate case
        std::error_code EC;
        static unsigned cnt = 0;
        auto filename = "incassert." + std::to_string(++cnt) + ".smt2";
        errs() << "Writing increment assert formula to '" << filename << "'..."
               << "\n";
        raw_fd_ostream File(filename, EC, sys::fs::OF_Text);
        m_ctx.toSmtLib(File);
      }
    });
    return r;
  }

  void visitVerifierAssertCall(CallBase &CB) {
    auto &f = *getCalledFunction(CB);

    Expr op = lookup(*CB.getOperand(0));
    if (f.getName().equals("verifier.assert.not"))
      op = boolop::lneg(op);
    doAssert(m_ctx.alu().getTrue(), op, CB);
  }

  void visitFatPointerInstr(CallBase &CB) {
    auto *f = getCalledFunction(CB);
    assert(f);

    if (f->getName().equals("__sea_set_extptr_slot0_hm")) {
      Expr ptr = lookup(*CB.getOperand(0));
      Expr data = lookup(*CB.getOperand(1));
      Expr res = m_ctx.mem().setFatData(ptr, 0 /*slot */, data);
      setValue(CB, res);
    } else if (f->getName().equals("__sea_set_extptr_slot1_hm")) {
      Expr ptr = lookup(*CB.getOperand(0));
      Expr data = lookup(*CB.getOperand(1));
      Expr res = m_ctx.mem().setFatData(ptr, 1 /*slot */, data);
      setValue(CB, res);
    } else if (f->getName().equals("__sea_get_extptr_slot0_hm")) {
      Expr ptr = lookup(*CB.getOperand(0));
      Expr res = m_ctx.mem().getFatData(ptr, 0 /*slot */);
      setValue(CB, res);
    } else if (f->getName().equals("__sea_get_extptr_slot1_hm")) {
      Expr ptr = lookup(*CB.getOperand(0));
      Expr res = m_ctx.mem().getFatData(ptr, 1 /*slot */);
      setValue(CB, res);
    } else if (f->getName().equals("__sea_copy_extptr_slots_hm")) {
      // convention is copy(dst, src)
      Expr dst = lookup(*CB.getOperand(0));
      Expr src = lookup(*CB.getOperand(1));

      Expr slot0_data = m_ctx.mem().getFatData(src, 0 /*slot */);
      Expr slot1_data = m_ctx.mem().getFatData(src, 1 /*slot */);
      Expr res = m_ctx.mem().setFatData(dst, 0 /*slot */, slot0_data);
      res = m_ctx.mem().setFatData(res, 1 /*slot */, slot1_data);
      setValue(CB, res);
    } else if (f->getName().equals("__sea_recover_pointer_hm")) {
      Expr fat_ptr = lookup(*CB.getOperand(0));
      setValue(CB, fat_ptr);
    }
  }

  void visitIndirectCall(CallBase &CB) {
    if (CB.getType()->isVoidTy()) {
      LOG("opsem",
          WARN << "Interpreting indirect call as noop: " << CB << "\n";);
      return;
    }
    // treat as non-det and issue a warning
    setValue(CB, Expr());
  }

  void visitVerifierAssumeCall(CallBase &CB) {
    // ignore assumes annotaed with "unified.assume"
    if (isUnifiedAssume(CB))
      return;
    auto &f = *getCalledFunction(CB);

    Expr op = lookup(*CB.getOperand(0));
    assert(op);

    if (f.getName().equals("verifier.assume.not"))
      op = boolop::lneg(op);

    if (!isOpX<TRUE>(op)) {
      m_ctx.addScopedSide(
          boolop::lor(m_ctx.read(m_sem.errorFlag(*(CB.getParent()))), op));
    }
  }

  void visitCallocCall(CallBase &CB) {
    if (!m_ctx.getMemReadRegister() || !m_ctx.getMemReadRegister()) {
      LOG("opsem", WARN << "treating calloc() as nop";);
      return;
    }

    assert(!m_ctx.isMemScalar());

    if (IgnoreCalloc2) {
      LOG("opsem", WARN << "treating calloc() as malloc()";);
      m_ctx.addDef(m_ctx.read(m_ctx.getMemWriteRegister()),
                   m_ctx.read(m_ctx.getMemReadRegister()));
    } else {
      LOG("opsem", WARN << "allowing calloc() to "
                           "zero initialize ALL of its memory region\n";);
      m_ctx.addDef(m_ctx.read(m_ctx.getMemWriteRegister()),
                   m_ctx.mem().zeroedMemory());
    }

    // get a fresh pointer
    setValue(CB, havoc(CB));
  }

  void visitShadowMemCall(CallBase &CB) {
    const auto &F = *getCalledFunction(CB);
    if (F.getName().equals("shadow.mem.init")) {
      unsigned id = shadow_dsa::getShadowId(CB);
      (void)id;
      assert(id >= 0);
      setValue(CB, havoc(CB));
      return;
    }

    if (F.getName().equals("shadow.mem.load")) {
      const Value &v = *CB.getOperand(1);
      Expr reg = m_ctx.mkRegister(v);
      m_ctx.read(reg);
      m_ctx.setMemReadRegister(reg);
      m_ctx.setMemScalar(extractUniqueScalar(CB) != nullptr);
      return;
    }

    if (F.getName().equals("shadow.mem.trsfr.load")) {
      const Value &v = *CB.getOperand(1);
      Expr reg = m_ctx.mkRegister(v);
      m_ctx.read(reg);
      m_ctx.setMemTrsfrReadReg(reg);
      if (extractUniqueScalar(CB) != nullptr) {
        WARN << "unexpected unique scalar in mem.trsfr.load: " << CB;
        llvm_unreachable(nullptr);
      }
      return;
    }

    if (F.getName().equals("shadow.mem.store")) {
      Expr memOut = m_ctx.mkRegister(CB);
      Expr memIn = m_ctx.getRegister(*CB.getOperand(1));
      m_ctx.read(memIn);
      setValue(CB, havoc(CB));

      m_ctx.setMemReadRegister(memIn);
      m_ctx.setMemWriteRegister(memOut);
      m_ctx.setMemScalar(extractUniqueScalar(CB) != nullptr);

      LOG("opsem.mem.store", errs() << "mem.store: " << CB << "\n";
          errs() << "arg1: " << *CB.getOperand(1) << "\n";
          errs() << "mem.store: memIn is " << *memIn << " memOut is " << *memOut
                 << "\n";);
      return;
    }

    if (F.getName().equals("shadow.mem.arg.ref")) {
      m_ctx.pushParameter(lookup(*CB.getOperand(1)));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.mod")) {
      m_ctx.pushParameter(lookup(*CB.getOperand(1)));
      Expr reg = m_ctx.mkRegister(CB);
      assert(reg);
      m_ctx.pushParameter(m_ctx.havoc(reg));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.new")) {
      Expr reg = m_ctx.mkRegister(CB);
      m_ctx.pushParameter(m_ctx.havoc(reg));
      return;
    }

    const Function &PF = *CB.getParent()->getParent();

    if (F.getName().equals("shadow.mem.in")) {
      if (PF.getName().equals("main"))
        setValue(CB, havoc(CB));
      else
        lookup(*CB.getOperand(1));
      return;
    }

    if (F.getName().equals("shadow.mem.out")) {
      if (PF.getName().equals("main"))
        setValue(CB, havoc(CB));
      else
        lookup(*CB.getOperand(1));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.init")) {
      if (PF.getName().equals("main"))
        setValue(CB, havoc(CB));
      return;
    }

    if (F.getName().equals("shadow.mem.global.init")) {
      Expr memOut = m_ctx.mkRegister(CB);
      Expr memIn = m_ctx.getRegister(*CB.getOperand(1));
      m_ctx.read(memIn);
      setValue(CB, lookup(*CB.getOperand(1)));

      m_ctx.setMemReadRegister(memIn);
      m_ctx.setMemWriteRegister(memOut);

      LOG("opsem.mem.global.init", errs() << "mem.global.init: " << CB << "\n";
          errs() << "arg1: " << *CB.getOperand(1) << "\n";
          errs() << "memIn: " << *memIn << ", memOut: " << *memOut << "\n";);

      Value *gVal = (*CB.getOperand(2)).stripPointerCasts();
      if (auto *gv = dyn_cast<llvm::GlobalVariable>(gVal)) {
        auto gvVal = m_ctx.getGlobalVariableInitValue(*gv);
        if (gvVal.first && (MaxSizeGlobalVarInit == 0 ||
                            gvVal.second <= MaxSizeGlobalVarInit)) {
          m_ctx.MemFill(lookup(*gv), gvVal.first, gvVal.second);
        } else {
          WARN << "skipping global var init of " << CB << " to " << *gVal
               << "\n";
        }
      }
      return;
    }

    WARN << "unknown shadow.mem call: " << CB;
    llvm_unreachable(nullptr);
  }

  void visitNondetCall(CallBase &CB) {
    if (!CB.getType()->isVoidTy()) {
      setValue(CB, m_ctx.havoc(m_ctx.mkRegister(CB)));
    }
  }
  void visitExternalCall(CallBase &CB) {
    auto &F = *getCalledFunction(CB);
    if (F.getFunctionType()->getReturnType()->isVoidTy())
      return;

    if (!EnableModelExternalCalls2 ||
        std::find(IgnoreExternalFunctions2.begin(),
                  IgnoreExternalFunctions2.end(),
                  F.getName()) != IgnoreExternalFunctions2.end()) {
      setValue(CB, Expr());
      return;
    }

    // Treat the call as an uninterpreted function
    Expr res;
    ExprVector fargs;
    ExprVector sorts;
    fargs.reserve(CB.data_operands_size());
    sorts.reserve(CB.data_operands_size());

    bool is_typed = true;
    for (auto &a : CB.data_ops()) {
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
      Expr symReg = m_ctx.mkRegister(CB);
      Expr ty = bind::typeOf(symReg);
      if (!ty) {
        is_typed = false;
      } else {
        sorts.push_back(ty);
      }
    }

    if (is_typed) {
      LOG("opsem",
          errs() << "Modelling " << CB << " with an uninterpreted function\n";);
      Expr name = mkTerm<const Function *>(getCalledFunction(CB), m_efac);
      Expr d = bind::fdecl(name, sorts);
      res = bind::fapp(d, fargs);
    }

    setValue(CB, res);
  }

  void visitKnownFunctionCall(CallBase &CB) {
    const Function &F = *getCalledFunction(CB);
    const FunctionInfo &fi = m_sem.getFunctionInfo(F);
    const BasicBlock &BB = *CB.getParent();

    // enabled
    m_ctx.setParameter(0, m_ctx.getPathCond()); // path condition
    // error flag in
    m_ctx.setParameter(1, m_ctx.read(m_sem.errorFlag(BB)));
    // error flag out
    m_ctx.setParameter(2, m_ctx.havoc(m_sem.errorFlag(BB)));
    for (const Argument *arg : fi.args)
      m_ctx.pushParameter(lookup(*CB.getOperand(arg->getArgNo())));
    for (const GlobalVariable *gv : fi.globals)
      m_ctx.pushParameter(lookup(*gv));

    if (fi.ret) {
      Expr reg = m_ctx.mkRegister(CB);
      Expr v = m_ctx.havoc(reg);
      setValue(CB, v);
      m_ctx.pushParameter(v);
    }

    LOG(
        "arg_error",

        if (m_ctx.getParameters().size() != bind::domainSz(fi.sumPred)) {
          const Function &PF = *BB.getParent();
          errs() << "Call instruction: " << CB << "\n";
          errs() << "Caller: " << PF << "\n";
          errs() << "Callee: " << F << "\n";
          // errs () << "Sum predicate: " << *fi.sumPred << "\n";
          errs() << "m_ctx.getParameters().size: "
                 << m_ctx.getParameters().size() << "\n";
          errs() << "Domain size: " << bind::domainSz(fi.sumPred) << "\n";
          errs() << "m_ctx.getParameters()\n";
          for (auto r : m_ctx.getParameters())
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

    assert(m_ctx.getParameters().size() == bind::domainSz(fi.sumPred));
    m_ctx.addSide(bind::fapp(fi.sumPred, m_ctx.getParameters()));

    m_ctx.resetParameters();
    m_ctx.pushParameter(falseE);
    m_ctx.pushParameter(falseE);
    m_ctx.pushParameter(falseE);
  }

  bool expandCallInst(CallInst &I,
                      std::function<bool(CallInst &)> InstExpandFn) {
    // -- The code is tricky because we must update
    // -- (a) instruction iterator inside m_ctx to point to newly expanded
    // --     instruction
    // -- (b) COI filter to include new instructions if they came from marked
    // instruction

    // -- remember if the current instruction is in the COI (cone of
    // -- influence). filter. If it is, we need to mark expanded instructions
    // -- to be in the cone as well
    bool isInFilter = m_sem.isInFilter(I);
    // -- get an iterator to the current instruction so that we can access
    // -- prev and next instructions
    BasicBlock::iterator me(&I);

    // -- remember the following instruction
    auto nextInst = me;
    // -- advance iterator to point to the next instruction from I
    ++nextInst;

    // -- check whether the current instruction is the first instruction of
    // -- the basic block and has no predecessor
    BasicBlock *bb = I.getParent();
    bool atBegin(bb->begin() == me);

    // -- if I is not the first instruction, make `me` point to the
    // predecessor of I
    if (!atBegin)
      --me;

    // -- expand I by lowering it into 0 or more other instructions
    if (!InstExpandFn(I))
      // -- return if expansion has failed
      return false;

    // -- restore instruction pointer to the new lowered instructions
    // -- the instruction pointer is either the first instruction of the basic
    // -- block or the instruction currently following `me`
    auto top = atBegin ? &*bb->begin() : &*(++me);
    // -- tell context that next instruction to execute is top, and that
    // -- execution of current instruction must be repeated (because the
    // -- current instruction has changed)
    m_ctx.setInstruction(*top, true);

    // -- update COI filter. New instructions introduced by lowering, if any,
    // -- are the instructions between current top, and whatever instruction
    // -- was following I
    if (isInFilter) {
      for (auto it = BasicBlock::iterator(top); it != nextInst; ++it) {
        m_sem.addToFilter(*it);
      }
    }
    return true;
  }

  void visitIntrinsicInst(IntrinsicInst &I) {
    switch (I.getIntrinsicID()) {
    case Intrinsic::bswap:
    case Intrinsic::expect:
    case Intrinsic::ctpop:
    case Intrinsic::ctlz:
    case Intrinsic::cttz:

      // -- unsupported intrinsics
    case Intrinsic::stacksave:
    case Intrinsic::stackrestore:
    case Intrinsic::get_dynamic_area_offset:
    case Intrinsic::returnaddress:
    case Intrinsic::frameaddress:
    case Intrinsic::prefetch:

    case Intrinsic::pcmarker:
    case Intrinsic::readcyclecounter:

    case Intrinsic::eh_typeid_for:

    case Intrinsic::flt_rounds:

    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end: {
      // -- use existing LLVM codegen to lower intrinsics into simpler
      // -- instructions that we support
      expandCallInst(I, [&m_sem = m_sem](CallInst &II) {
        IntrinsicLowering IL(m_sem.getDataLayout());
        IL.LowerIntrinsicCall(&II);
        return true;
      });
    } break;
    case Intrinsic::sadd_with_overflow: {
      Type *ty = I.getOperand(0)->getType();
      Expr op0;
      Expr op1;
      GetOpExprs(I, op0, op1);

      // assume doAdd has same bitwidth as Op0
      Expr add_res = m_ctx.alu().doAdd(op0, op1, ty->getScalarSizeInBits());
      Expr is_overflow =
          m_ctx.alu().IsSaddNoOverflow(op0, op1, ty->getScalarSizeInBits());
      Expr is_underflow =
          m_ctx.alu().IsBaddNoUnderflow(op0, op1, ty->getScalarSizeInBits());
      if (!add_res || !is_overflow || !is_underflow) {
        LOG("opsem", WARN << "An operation returned null:" << I);
        setValue(I, Expr());
      } else {
        Expr is_carry = m_ctx.alu().doNot(
            m_ctx.alu().doAnd(is_overflow, is_underflow, 1 /* bitwidth */),
            1 /* bitwidth*/);
        setValue(I, createArithmeticWithOverflowRecord(
                        add_res, is_carry, ty->getScalarSizeInBits(),
                        getCarryBitPadWidth(I)));
      }
    } break;
    case Intrinsic::uadd_with_overflow: {
      Type *ty = I.getOperand(0)->getType();
      Expr op0;
      Expr op1;
      GetOpExprs(I, op0, op1);

      // assume doAdd has same bitwidth as Op0
      Expr add_res = m_ctx.alu().doAdd(op0, op1, ty->getScalarSizeInBits());
      Expr is_overflow =
          m_ctx.alu().IsUaddNoOverflow(op0, op1, ty->getScalarSizeInBits());
      if (!add_res || !is_overflow) {
        LOG("opsem", WARN << "An operation returned null:" << I);
        setValue(I, Expr());
      } else {
        Expr is_carry = m_ctx.alu().doNot(is_overflow, 1 /* bitwidth */);
        setValue(I, createArithmeticWithOverflowRecord(
                        add_res, is_carry, ty->getScalarSizeInBits(),
                        getCarryBitPadWidth(I)));
      }
    } break;
    case Intrinsic::uadd_sat: {
      Type *ty = I.getOperand(0)->getType();
      Expr op0, op1;
      GetOpExprs(I, op0, op1);
      assert(op0 && op1);
      Expr addRes = m_ctx.alu().doAdd(op0, op1, ty->getScalarSizeInBits());
      Expr isNoOverflow =
          m_ctx.alu().IsUaddNoOverflow(op0, op1, ty->getScalarSizeInBits());
      assert(addRes && isNoOverflow);
      mpz_class maxValZ;
      for (unsigned i = 0; i < ty->getScalarSizeInBits(); ++i) {
        maxValZ.setbit(i);
      }
      Expr maxVal = m_ctx.alu().num(maxValZ, ty->getScalarSizeInBits());
      Expr res = boolop::lite(isNoOverflow, addRes, maxVal);
      setValue(I, res);
    } break;
    case Intrinsic::ssub_with_overflow: {
      Type *ty = I.getOperand(0)->getType();
      Expr op0;
      Expr op1;
      GetOpExprs(I, op0, op1);

      // assume doSub has same bitwidth as Op0
      Expr sub_res = m_ctx.alu().doSub(op0, op1, ty->getScalarSizeInBits());
      Expr is_overflow =
          m_ctx.alu().IsBsubNoOverflow(op0, op1, ty->getScalarSizeInBits());
      Expr is_underflow =
          m_ctx.alu().IsSsubNoUnderflow(op0, op1, ty->getScalarSizeInBits());
      if (!sub_res || !is_overflow || !is_underflow) {
        LOG("opsem", WARN << "An operation returned null:" << I);
        setValue(I, Expr());
      } else {
        Expr is_carry = m_ctx.alu().doNot(
            m_ctx.alu().doAnd(is_overflow, is_underflow, 1 /* bitwidth */),
            1 /* bitwidth*/);
        setValue(I, createArithmeticWithOverflowRecord(
                        sub_res, is_carry, ty->getScalarSizeInBits(),
                        getCarryBitPadWidth(I)));
      }
    } break;
    case Intrinsic::usub_with_overflow: {
      Type *ty = I.getOperand(0)->getType();
      Expr op0;
      Expr op1;
      GetOpExprs(I, op0, op1);

      // assume doSub has same bitwidth as Op0
      Expr sub_res = m_ctx.alu().doSub(op0, op1, ty->getScalarSizeInBits());
      Expr is_underflow =
          m_ctx.alu().IsUsubNoUnderflow(op0, op1, ty->getScalarSizeInBits());
      if (!sub_res || !is_underflow) {
        LOG("opsem", WARN << "An operation returned null:" << I);
        setValue(I, Expr());
      } else {
        Expr is_carry = m_ctx.alu().doNot(is_underflow, 1 /* bitwidth */);
        setValue(I, createArithmeticWithOverflowRecord(
                        sub_res, is_carry, ty->getScalarSizeInBits(),
                        getCarryBitPadWidth(I)));
      }
    } break;
    case Intrinsic::smul_with_overflow: {
      Type *ty = I.getOperand(0)->getType();
      Expr op0;
      Expr op1;
      GetOpExprs(I, op0, op1);

      // assume doMul has same bitwidth as Op0
      Expr mul_res = m_ctx.alu().doMul(op0, op1, ty->getScalarSizeInBits());
      Expr is_overflow =
          m_ctx.alu().IsSmulNoOverflow(op0, op1, ty->getScalarSizeInBits());
      Expr is_underflow =
          m_ctx.alu().IsBmulNoUnderflow(op0, op1, ty->getScalarSizeInBits());
      if (!mul_res || !is_overflow || !is_underflow) {
        LOG("opsem", WARN << "An operation returned null:" << I);
        setValue(I, Expr());
      } else {
        Expr is_carry = m_ctx.alu().doNot(
            m_ctx.alu().doAnd(is_overflow, is_underflow, 1 /* bitwidth */),
            1 /* bitwidth*/);
        setValue(I, createArithmeticWithOverflowRecord(
                        mul_res, is_carry, ty->getScalarSizeInBits(),
                        getCarryBitPadWidth(I)));
      }
    } break;
    case Intrinsic::umul_with_overflow: {
      Type *ty = I.getOperand(0)->getType();
      Expr op0;
      Expr op1;
      GetOpExprs(I, op0, op1);

      // assume doMul has same bitwidth as Op0
      Expr mul_res = m_ctx.alu().doMul(op0, op1, ty->getScalarSizeInBits());
      Expr is_overflow =
          m_ctx.alu().IsUmulNoOverflow(op0, op1, ty->getScalarSizeInBits());
      if (!mul_res || !is_overflow) {
        LOG("opsem", WARN << "An operation returned null:" << I);
        setValue(I, Expr());
      } else {
        Expr is_carry = m_ctx.alu().doNot(
            m_ctx.alu().doAnd(is_overflow, is_overflow, 1 /* bitwidth */),
            1 /* bitwidth*/);
        setValue(I, createArithmeticWithOverflowRecord(
                        mul_res, is_carry, ty->getScalarSizeInBits(),
                        getCarryBitPadWidth(I)));
      }
    } break;
    case Intrinsic::smax:
    case Intrinsic::smin:
    case Intrinsic::umax:
    case Intrinsic::umin: {
      // llvm.<sign_type>max.<type>(<type> %a, <type> %b) Intrinsic can be
      // converted into:
      //  %a >_sign_type %b ? %a : %b
      // similar for llvm.umin
      //  %a <_sign_type %b ? %a : %b
      Type *ty = I.getOperand(0)->getType();
      Expr op0;
      Expr op1;
      GetOpExprs(I, op0, op1);

      bool is_signed = I.getIntrinsicID() == Intrinsic::smax ||
                       I.getIntrinsicID() == Intrinsic::smin;
      bool is_max = I.getIntrinsicID() == Intrinsic::smax ||
                    I.getIntrinsicID() == Intrinsic::umax;
      Expr cond;
      if (is_signed) {
        if (is_max) {
          cond = m_ctx.alu().doSgt(op0, op1, ty->getScalarSizeInBits());
        } else {
          cond = m_ctx.alu().doSlt(op0, op1, ty->getScalarSizeInBits());
        }
      } else {
        if (is_max) {
          cond = m_ctx.alu().doUgt(op0, op1, ty->getScalarSizeInBits());
        } else {
          cond = m_ctx.alu().doUlt(op0, op1, ty->getScalarSizeInBits());
        }
      }
      if (!cond) {
        LOG("opsem", WARN << "An operation returned null:" << I);
        setValue(I, Expr());
      } else {
        Expr res = bind::lite(cond, op0, op1);
        setValue(I, res);
      }
    } break;
    default:
      // interpret by non-determinism (and a warning)
      if (!I.getType()->isVoidTy())
        setValue(I, Expr());
    }
  }

  void GetOpExprs(const IntrinsicInst &I, Expr &op0, Expr &op1) {
    op0 = lookup(*I.getOperand(0));
    op1 = lookup(*I.getOperand(1));
  }

  unsigned getCarryBitPadWidth(IntrinsicInst &I) {
    const DataLayout &DL = m_sem.getDataLayout();
    Type *curTy = I.getType();
    auto *STy = dyn_cast<StructType>(curTy);
    const StructLayout *SL = DL.getStructLayout(STy);
    auto struc_size_in_bits = SL->getSizeInBits();
    auto offset_in_bits = SL->getElementOffsetInBits(1);
    auto carry_size_in_bits = (STy->getElementType(1))->getScalarSizeInBits();
    return struc_size_in_bits - offset_in_bits - carry_size_in_bits;
  }

  Expr createArithmeticWithOverflowRecord(Expr &opResult, Expr &carryBit,
                                          unsigned opResultBitWidth,
                                          unsigned carryBitPadwidth) {
    Expr carry = m_ctx.alu().Concat(
        {m_ctx.alu().ui(0U, carryBitPadwidth), carryBitPadwidth},
        {carryBit, 1});
    return m_ctx.alu().Concat({carry, carryBitPadwidth},
                              {opResult, opResultBitWidth});
  }

  void visitDbgDeclareInst(DbgDeclareInst &I) { /* nothing */
  }
  void visitDbgValueInst(DbgValueInst &I) { /* nothing */
  }
  void visitDbgInfoIntrinsic(DbgInfoIntrinsic &I) { /* nothing */
  }

  void visitMemSetInst(MemSetInst &I) {
    Expr v = executeMemSetInst(*I.getDest(), *I.getValue(), *I.getLength(),
                               I.getDestAlignment(), m_ctx);
    if (!v)
      WARN << "skipped memset: " << I << "\n";
  }
  void visitMemCpyInst(MemCpyInst &I) {
    executeMemCpyInst(*I.getDest(), *I.getSource(), *I.getLength(),
                      I.getDestAlignment(), m_ctx);
  }

  void visitMemMoveInst(MemMoveInst &I) {
    // -- our implementation of memcpy is actually memmove
    executeMemCpyInst(*I.getDest(), *I.getSource(), *I.getLength(),
                      I.getDestAlignment(), m_ctx);
  }
  void visitMemTransferInst(MemTransferInst &I) {
    LOG("opsem", errs() << "Unknown memtransfer: " << I << "\n";);
    assert(0);
  }

  void visitMemIntrinsic(MemIntrinsic &I) {
    LOG("opsem", errs() << "Unknown memory intrinsic: " << I << "\n";);
    assert(0);
  }

  void visitVAStartInst(VAStartInst &I) { assert(0); }
  void visitVAEndInst(VAEndInst &I) { assert(0); }
  void visitVACopyInst(VACopyInst &I) { assert(0); }

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
    Expr val = executeExtractElementInst(I.getType(), *I.getOperand(0),
                                         *I.getOperand(1), m_ctx);
    setValue(I, val);
  }

  Expr executeExtractElementInst(Type *retTy, Value &vec, Value &idx,
                                 Bv2OpSemContext &ctx) {
    Expr res;

    Expr valE = lookup(vec);
    if (!valE)
      return res;

    const DataLayout &DL = m_sem.getDataLayout();

    auto vecSz = DL.getTypeSizeInBits(vec.getType());

    // -- this is also the size of vector element
    auto retSz = DL.getTypeSizeInBits(retTy);
    if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&idx)) {

      auto begin = retSz * ci->getZExtValue();
      auto end = begin + retSz - 1;
      res = m_ctx.alu().Extract({valE, vecSz}, begin, end);
    } else {
      LOG("opsem", WARN << "unsupported extractelement with non-constant index "
                           "operand\n";);
      llvm_unreachable("unsupported");
    }

    return res;
  }
  void visitInsertElementInst(InsertElementInst &I) {
    Expr val =
        executeInsertElementInst(I.getType(), *I.getOperand(0),
                                 *I.getOperand(1), *I.getOperand(2), m_ctx);
    setValue(I, val);
  }

  Expr executeInsertElementInst(Type *retTy, Value &vecValue, Value &elmt,
                                Value &idx, Bv2OpSemContext &ctx) {

    Expr res;
    Expr valE = lookup(vecValue);
    Expr elmtE = lookup(elmt);
    if (!valE || !elmtE)
      return res;

    const DataLayout &DL = m_sem.getDataLayout();
    auto vecSz = DL.getTypeSizeInBits(vecValue.getType());
    auto elmtSz = DL.getTypeSizeInBits(elmt.getType());

    if (vecSz == elmtSz)
      return elmtE;
    assert(vecSz > elmtSz);
    assert(vecSz % elmtSz == 0);

    if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&idx)) {
      unsigned idxV = ci->getZExtValue();

      // -- first bit
      unsigned begin = idxV * elmtSz;
      // -- last bit
      unsigned end = begin + elmtSz - 1;

      Expr suffix;
      unsigned suffixSz = 0;
      Expr prefix;
      unsigned prefixSz = 0;

      if (begin > 0) {
        suffixSz = begin;
        suffix = m_ctx.alu().Extract({valE, vecSz}, 0, begin - 1);
      }
      if (end < vecSz - 1) {
        prefixSz = vecSz - 1 - end;
        prefix = m_ctx.alu().Extract({valE, vecSz}, end + 1, vecSz - 1);
      }

      unsigned res_sz = 0;

      if (suffixSz > 0) {
        res = suffix;
        res_sz += suffixSz;
      }

      if (res_sz) {
        res = m_ctx.alu().Concat({elmtE, elmtSz}, {res, res_sz});
        res_sz += elmtSz;
      } else {
        res = elmtE;
        res_sz = elmtSz;
      }

      if (prefixSz > 0) {
        res = m_ctx.alu().Concat({prefix, prefixSz}, {res, res_sz});
        res_sz += prefixSz;
        (void)res_sz;
      }
    } else {
      LOG("opsem",
          WARN
              << "unsupported insertlement with non-constant index operand\n";);
      llvm_unreachable("unsupported");
    }
    return res;
  }
  void visitShuffleVectorInst(ShuffleVectorInst &I) {
    llvm_unreachable(nullptr);
  }

  void visitExtractValueInst(ExtractValueInst &I) {
    if (!I.hasIndices()) {
      ERR << I;
      llvm_unreachable("At least one index must be specified.");
    }
    Expr val = executeExtractValueInst(I.getType(), *I.getAggregateOperand(),
                                       I.getIndices(), m_ctx);
    setValue(I, val);
  }

  Expr executeExtractValueInst(Type *retTy, Value &aggValue,
                               ArrayRef<unsigned> indices,
                               Bv2OpSemContext &ctx) {
    Expr aggOp = lookup(aggValue);
    if (!aggOp) {
      return Expr();
    }
    // compute the offsets: begin and end of bits to extract from aggOp
    const DataLayout DL = m_sem.getDataLayout();
    Type *curTy = aggValue.getType();
    uint64_t begin = 0, end = 0;
    for (unsigned idx : indices) {
      if (auto *STy = dyn_cast<StructType>(curTy)) {
        // current struct agg type
        const StructLayout *SL = DL.getStructLayout(STy);
        curTy = STy->getElementType(idx);
        begin += SL->getElementOffsetInBits(idx);
      } else if (auto *ATy = dyn_cast<ArrayType>(curTy)) {
        // handle array agg type
        curTy = ATy->getElementType();
        uint64_t EltSize = DL.getTypeSizeInBits(curTy);
        begin += idx * EltSize;
      } else {
        errs() << "Unhandled aggregate type to extract from: " << *curTy
               << "\n";
        llvm_unreachable(nullptr);
      }
    }
    assert(curTy->getTypeID() == retTy->getTypeID());
    end = begin + DL.getTypeSizeInBits(retTy) - 1;
    Expr res = m_ctx.alu().Extract(
        {aggOp, aggValue.getType()->getScalarSizeInBits()}, begin, end);
    // ensure that result is a pointer type after it has been extracted from the
    // struct
    if (retTy->isPointerTy())
      res = ctx.mem().inttoptr(res, *DL.getIntPtrType(retTy), *retTy);
    return res;
  }

  void visitInsertValueInst(InsertValueInst &I) {
    if (!I.hasIndices()) {
      ERR << I;
      llvm_unreachable("At least one index must be specified.");
    }
    Expr val = executeInsertValueInst(*I.getAggregateOperand(),
                                      *I.getInsertedValueOperand(),
                                      I.getIndices(), m_ctx);
    setValue(I, val);
  }

  Expr executeInsertValueInst(Value &aggVal, Value &insertedVal,
                              ArrayRef<unsigned> indices,
                              Bv2OpSemContext &ctx) {
    Expr aggOp = lookup(aggVal);
    Expr insertedOp = lookup(insertedVal);
    if (!aggOp || !insertedOp) {
      return Expr();
    }
    // compute the offsets: begin and end of bits to extract from aggOp
    const DataLayout &DL = m_sem.getDataLayout();
    Type *curTy = aggVal.getType();
    uint64_t begin = 0, end = 0;
    for (unsigned idx : indices) {
      if (auto *STy = dyn_cast<StructType>(curTy)) {
        // current struct agg type
        const StructLayout *SL = DL.getStructLayout(STy);
        curTy = STy->getElementType(idx);
        begin += SL->getElementOffsetInBits(idx);
      } else if (auto *ATy = dyn_cast<ArrayType>(curTy)) {
        // handle array agg type
        curTy = ATy->getElementType();
        uint64_t EltSize = DL.getTypeSizeInBits(curTy);
        begin += idx * EltSize;
      } else {
        errs() << "Unhandled aggregate type to insert into" << *curTy << "\n";
        llvm_unreachable(nullptr);
      }
    }
    unsigned insertSize = DL.getTypeSizeInBits(insertedVal.getType());
    if (insertSize != DL.getTypeSizeInBits(curTy)) {
      llvm_unreachable("inserted value width not matched!");
    }
    unsigned aggSize = DL.getTypeSizeInBits(aggVal.getType());
    end = begin + insertSize - 1;

    Expr ret = insertedOp;
    if (insertedVal.getType()->isPointerTy())
      ret = m_ctx.ptrtoint(insertedOp, *insertedVal.getType(),
                           *DL.getIntPtrType(insertedVal.getType()));

    if (begin > 0)
      ret = m_ctx.alu().Concat(
          {ret, insertedVal.getType()->getScalarSizeInBits()},
          {m_ctx.alu().Extract({aggOp, aggVal.getType()->getScalarSizeInBits()},
                               0, begin - 1),
           begin});

    if (end < aggSize - 1)
      ret = m_ctx.alu().Concat(
          {m_ctx.alu().Extract({aggOp, aggVal.getType()->getScalarSizeInBits()},
                               end + 1, aggSize - 1),
           aggSize - end - 1},
          {ret, insertedVal.getType()->getScalarSizeInBits()});

    return ret;
  }

  void visitInstruction(Instruction &I) {
    ERR << I;
    llvm_unreachable("No semantics to this instruction yet!");
  }

  void visitFreezeInst(FreezeInst &I) {
    // operationally, freeze is a noop
    Expr res = lookup(*I.getOperand(0));
    setValue(I, res);
  }

  Expr executeSelectInst(Expr cond, Expr op0, Expr op1, Type *ty,
                         Bv2OpSemContext &ctx) {
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }
    if (!(cond && op0 && op1))
      return Expr(0);

    // -- push ite over a struct
    if (strct::isStructVal(op0))
      return strct::push_ite_struct(cond, op0, op1);
    // -- push ite over a lambda
    return bind::lite(cond, op0, op1);
  }

  Expr executeTruncInst(const Value &v, const Type &ty, Bv2OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();

    return ctx.alu().doTrunc(op0, m_sem.sizeInBits(ty));
  }

  Expr executeZExtInst(const Value &v, const Type &ty, Bv2OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();
    return ctx.alu().doZext(op0, m_sem.sizeInBits(ty), m_sem.sizeInBits(v));
  }

  Expr executeSExtInst(const Value &v, const Type &ty, Bv2OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();
    return ctx.alu().doSext(op0, m_sem.sizeInBits(ty), m_sem.sizeInBits(v));
  }

  Expr executeICMP_EQ(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doEq(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrEq(op0, op1);
    default:
      errs() << "Unhandled ICMP_EQ predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_NE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doNe(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrNe(op0, op1);
    default:
      errs() << "Unhandled ICMP_NE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_ULT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doUlt(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrUlt(op0, op1);
    default:
      errs() << "Unhandled ICMP_ULT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SLT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doSlt(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrSlt(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_UGT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doUgt(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrUgt(op0, op1);
    default:
      errs() << "Unhandled ICMP_UGT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SGT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {

    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doSgt(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrSgt(op0, op1);
    default:
      errs() << "Unhandled ICMP_SGT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_ULE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doUle(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrUle(op0, op1);
    default:
      errs() << "Unhandled ICMP_ULE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SLE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doSle(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrSle(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_UGE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doUge(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrUge(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SGE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return ctx.alu().doSge(op0, op1, ty->getScalarSizeInBits());
    case Type::PointerTyID:
      return ctx.mem().ptrSge(op0, op1);
    default:
      errs() << "Unhandled ICMP_SGE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executePtrToIntInst(const Value &op, const Type *ty,
                           Bv2OpSemContext &ctx) {
    Expr res = lookup(op);
    if (!res)
      return Expr();
    return ctx.ptrtoint(res, *op.getType(), *ty);
  }

  Expr executeIntToPtrInst(const Value &op, const Type *ty,
                           Bv2OpSemContext &ctx) {
    Expr res = lookup(op);
    if (!res)
      return Expr();
    return ctx.inttoptr(res, *op.getType(), *ty);
  }

  Expr executeGEPOperation(const Value &ptr, gep_type_iterator it,
                           gep_type_iterator end, Bv2OpSemContext &ctx) {
    Expr addr = lookup(ptr);
    return addr ? ctx.gep(addr, it, end) : Expr();
  }

  Expr executeLoadInst(const Value &addr, unsigned alignment, const Type *ty,
                       Bv2OpSemContext &ctx) {
    Expr res;
    if (!ctx.getMemReadRegister())
      return res;

    // XXX avoid reading address if current read is from a scalar
    Expr op0 = ctx.isMemScalar() ? Expr(nullptr) : lookup(addr);
    res = ctx.loadValueFromMem(op0, *ty, alignment);
    ctx.setMemReadRegister(Expr());
    return res;
  }

  Expr executeStoreInst(const Value &val, const Value &addr, unsigned alignment,
                        Bv2OpSemContext &ctx) {

    // -- fn to update ctx in case the store operation is treated as a noop
    auto noop = [&ctx]() {
      Expr res = ctx.read(ctx.getMemReadRegister());
      ctx.write(ctx.getMemWriteRegister(), res);
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return res;
    };

    if (val.getType()->isDoubleTy() || val.getType()->isFloatTy()) {
      if (ctx.getMemReadRegister() && ctx.getMemWriteRegister()) {
        LOG("opsem", WARN << "treating double/float store as noop: *" << addr
                          << " := " << val << "\n";);

        return noop();
      }
      // if anything above fails, continue as usual. Exceptional cases are
      // treated as memhavoc below.
    }

    if (!ctx.getMemReadRegister() || !ctx.getMemWriteRegister() ||
        m_sem.isSkipped(val)) {
      LOG("opsem",
          WARN << "skipping store to " << addr << " of " << val << "\n";);
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return Expr();
    }

    if (isa<UndefValue>(val)) {
      // from LLVM Lang Ref:
      // A store of an undefined value can be assumed to not have any effect;
      return noop();
    }

    Expr v = lookup(val);
    // XXX avoid reading address if current read is from a scalar
    Expr p = ctx.isMemScalar() ? Expr(nullptr) : lookup(addr);
    Expr res = ctx.storeValueToMem(v, p, *val.getType(), alignment);

    LOG("opsem",
        if (!res) WARN << "Failed store to " << addr << " of " << val << "\n";);

    ctx.setMemReadRegister(Expr());
    ctx.setMemWriteRegister(Expr());
    return res;
  }

  Expr executeMemSetInst(const Value &dst, const Value &val,
                         const Value &length, unsigned alignment,
                         Bv2OpSemContext &ctx) {
    if (!ctx.getMemReadRegister() || !ctx.getMemWriteRegister() ||
        m_sem.isSkipped(dst) || m_sem.isSkipped(val)) {
      LOG("opsem", WARN << "skipping memset because";
          if (m_sem.isSkipped(dst)) WARN << "\tskipped dst: " << dst;
          if (m_sem.isSkipped(val)) WARN << "\tskipped val: " << val;
          if (!ctx.getMemReadRegister()) WARN << "\tno read register set";
          if (!ctx.getMemWriteRegister()) WARN << "\tno write register set";);
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return Expr();
    }

    if (ctx.isMemScalar()) {
      LOG("opsem", ERR << "memset to scalars is not supported";);
      llvm_unreachable(nullptr);
    }

    Expr res;
    Expr addr = lookup(dst);

    assert(val.getType()->isIntegerTy(8));
    Expr v = lookup(val);
    Expr len = lookup(length);
    if (v && addr) {
      if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&length)) {
        res = m_ctx.MemSet(addr, v, ci->getZExtValue(), alignment);
      } else if (len) {
        res = m_ctx.MemSet(addr, v, len, alignment);
      }
    }

    if (!res)
      LOG("opsem", WARN << "interpreting memset as noop\n";);

    ctx.setMemReadRegister(Expr());
    ctx.setMemWriteRegister(Expr());
    return res;
  }

  Expr executeMemCpyInst(const Value &dst, const Value &src,
                         const Value &length, unsigned alignment,
                         Bv2OpSemContext &ctx) {
    if (!ctx.getMemReadRegister() || !ctx.getMemWriteRegister() ||
        !ctx.getMemTrsfrReadReg() || m_sem.isSkipped(dst) ||
        m_sem.isSkipped(src)) {
      LOG("opsem",
          WARN << "skipping memcpy due to src argument: " << src << "\n";);
      ctx.setMemTrsfrReadReg(Expr());
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return Expr();
    }

    if (ctx.isMemScalar())
      llvm_unreachable("memcpy to scalars is not supported");

    Expr res;
    Expr dstAddr = lookup(dst);
    Expr srcAddr = lookup(src);
    Expr len = lookup(length);
    if (dstAddr && srcAddr) {
      if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&length)) {
        res = m_ctx.MemCpy(dstAddr, srcAddr, ci->getZExtValue(), alignment);
      } else {
        res = m_ctx.MemCpy(dstAddr, srcAddr, len, alignment);
      }
    }

    if (!res)
      LOG("opsem", WARN << "interpreting memcpy as noop\n";);

    ctx.setMemTrsfrReadReg(Expr());
    ctx.setMemReadRegister(Expr());
    ctx.setMemWriteRegister(Expr());
    return res;
  }

  Expr executeBitCastInst(const Value &op, Type *ty, Bv2OpSemContext &ctx) {
    // -- opTy is destination type of the cast
    Type *opTy = op.getType();

    if (opTy->getTypeID() == llvm::Type::TypeID::ScalableVectorTyID ||
        ty->getTypeID() == llvm::Type::TypeID::ScalableVectorTyID)
      llvm_unreachable("Scalable Vector types are unsupported");

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
      else if (opTy->isIntegerTy() || opTy->isVectorTy()) {
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
    } else if (ty->isVectorTy()) {
      if (opTy->isIntegerTy() || opTy->isVectorTy())
        return res;
      else
        llvm_unreachable("bitcast from vector type is unsupported");
    }

    llvm_unreachable("Invalid bitcast");
  }

  void visitModule(Module &M) {
    LOG("opsem.module", errs() << M << "\n";);
    if (UseCrabInferRng || UseCrabLowerIsDeref || UseCrabCheckIsDeref) {
      m_sem.initCrabAnalysis(M);
      m_sem.runCrabAnalysis();
    }

    m_ctx.onModuleEntry(M);

    for (const Function &fn : M.functions()) {
      if (fn.hasAddressTaken()) {
        // XXX hard-coded. should be based on use
        // XXX some functions have their address taken for llvm.used
        if (fn.getName().equals("verifier.error") ||
            fn.getName().startswith("verifier.assume") ||
            fn.getName().equals("seahorn.fail") ||
            fn.getName().startswith("shadow.mem"))
          continue;
        if (m_sem.isSkipped(fn))
          continue;
        Expr symReg = m_ctx.mkRegister(fn);
        assert(symReg);
        setValue(fn, m_ctx.mem().falloc(fn));
      }
    }

    // -- allocate and layout globals
    for (const GlobalVariable &gv : M.globals()) {
      if (m_sem.isSkipped(gv))
        continue;
      if (gv.getSection().equals("llvm.metadata")) {
        LOG("opsem", WARN << "Skipping global variable marked "
                             "by llvm.metadata section: @"
                          << gv.getName(););
        continue;
      }
      if (gv.getName().equals("llvm.global_ctors") ||
          gv.getName().equals("llvm.global_dtors")) {
        continue;
      }
      Expr symReg = m_ctx.mkRegister(gv);
      assert(symReg);
      setValue(gv, m_ctx.mem().galloc(gv));
    }

    // initialize globals
    // must be done after allocations to deal with forward references
    for (const GlobalVariable &gv : M.globals()) {
      if (m_sem.isSkipped(gv))
        continue;
      if (gv.getSection().equals("llvm.metadata"))
        continue;
      if (gv.getName().equals("llvm.global_ctors") ||
          gv.getName().equals("llvm.global_dtors")) {
        continue;
      }
      m_ctx.mem().initGlobalVariable(gv);
    }

    LOG("opsem", m_ctx.mem().dumpGlobalsMap());
  }

  void visitBasicBlock(BasicBlock &BB) {
    Function &F = *BB.getParent();
    /// -- check if globals need to be initialized
    if (&F.getEntryBlock() == &BB) {
      if (F.getName().equals("main"))
        visitModule(*F.getParent());
      m_ctx.onFunctionEntry(*BB.getParent());
    }

    // read the error flag to make it live
    m_ctx.read(m_sem.errorFlag(BB));
  }
};

struct OpSemPhiVisitor : public InstVisitor<OpSemPhiVisitor>, OpSemVisitorBase {
  OpSemPhiVisitor(Bv2OpSemContext &ctx, Bv2OpSem &sem)
      : OpSemVisitorBase(ctx, sem) {}

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
      if (m_sem.isSkipped(*phi))
        continue;
      const Value &v = *phi->getIncomingValueForBlock(m_ctx.getPrevBb());
      ops.push_back(lookup(v));
    }

    // -- set values to all PHINode registers
    curr = BB.begin();
    for (unsigned i = 0; PHINode *phi = dyn_cast<PHINode>(curr); ++curr) {
      if (m_sem.isSkipped(*phi))
        continue;
      setValue(*phi, ops[i++]);
    }
  }
};
} // namespace details
} // namespace seahorn

namespace seahorn {
namespace details {
Bv2OpSemContext::Bv2OpSemContext(Bv2OpSem &sem, SymStore &values,
                                 ExprVector &side)
    : OpSemContext(values, side), m_sem(sem), m_func(nullptr), m_bb(nullptr),
      m_inst(nullptr), m_prev(nullptr), m_scalar(false) {
  zeroE = mkTerm<expr::mpz_class>(0UL, efac());
  oneE = mkTerm<expr::mpz_class>(1UL, efac());
  m_z3.reset(new EZ3(efac()));
  m_z3_simplifier.reset(new ZSimplifier<EZ3>(*m_z3));
  m_z3_solver.reset(new ZSolver<EZ3>(*m_z3, "QF_ABV"));
  auto &params = m_z3_simplifier->params();
  params.set("ctrl_c", true);
  params.set(":rewriter.flat", false);
  m_shouldSimplify = SimplifyExpr;
  m_shouldSimplifyNonMem = SimplifyExprNonMem;
  m_alu = mkBvOpSemAlu(*this);
  OpSemMemManager *mem = nullptr;

  unsigned ptrSize =
      PtrSize == 0 ? m_sem.getDataLayout().getPointerSize(0) : PtrSize;
  unsigned wordSize = WordSize == 0 ? ptrSize : WordSize;

  LOG("opsem",
      INFO << "pointer size: " << ptrSize << ", word size: " << wordSize;);

  if (UseFatMemory)
    mem = mkFatMemManager(m_sem, *this, ptrSize, wordSize, UseLambdas);
  else if (UseWideMemory) {
    mem = mkWideMemManager(m_sem, *this, ptrSize, wordSize, UseLambdas);
  } else if (UseExtraWideMemory) {
    if (UseTrackingMemory) {
      mem = mkTrackingExtraWideMemManager(m_sem, *this, ptrSize, wordSize,
                                          UseLambdas);
    } else {
      mem = mkExtraWideMemManager(m_sem, *this, ptrSize, wordSize, UseLambdas);
    }
  } else {
    mem = mkRawMemManager(m_sem, *this, ptrSize, wordSize, UseLambdas);
  }
  assert(mem);
  setMemManager(mem);
}

Bv2OpSemContext::Bv2OpSemContext(SymStore &values, ExprVector &side,
                                 const Bv2OpSemContext &o)
    : OpSemContext(values, side), m_sem(o.m_sem), m_func(o.m_func),
      m_bb(o.m_bb), m_inst(o.m_inst), m_prev(o.m_prev),
      m_readRegister(o.m_readRegister), m_writeRegister(o.m_writeRegister),
      m_scalar(o.m_scalar), m_trfrReadReg(o.m_trfrReadReg),
      m_fparams(o.m_fparams), m_ignored(o.m_ignored),
      m_registers(o.m_registers), m_memManager(nullptr), m_alu(nullptr),
      m_parent(&o), zeroE(o.zeroE), oneE(o.oneE), m_z3(o.m_z3),
      m_z3_simplifier(o.m_z3_simplifier), m_z3_solver(o.m_z3_solver) {
  setPathCond(o.getPathCond());
}

// If running in lambda mode,
// convert constant arrays returned by Z3 simplifier to a lambda.
//
// Details: When Z3 is given a lambda of the form lambda x: 0 to simplify, a
// constant array is returned. If running in lambda mode, this will cause the
// formula to have both lambdas and constant arrays which is not supported
// (fully) by Z3 and y2.
// This workaround fixes the issue by converting constant arrays gotten from
// Z3 back to lambda x: 0.
Expr coerceConstArrayToLambda(Expr e, ExprFactory &efac) {
  // go into structs until a non struct is found; convert to lambda if needed.
  if (strct::isStructVal(e)) {
    llvm::SmallVector<Expr, 8> kids;
    for (unsigned i = 0, sz = e->arity(); i < sz; ++i) {

      kids.push_back(coerceConstArrayToLambda(e->arg(i), efac));
    }
    return strct::mk(kids);
  } else if (isOpX<CONST_ARRAY>(e)) {
    Expr dom = e->arg(0); // get domain
    Expr val = e->arg(1); // get value
    Expr addr = bind::mkConst(mkTerm<std::string>("addr", efac), dom);
    Expr decl = bind::fname(addr);
    Expr res = mk<LAMBDA>(decl, val);
    return res;
  } else {
    return e;
  }
}

Expr Bv2OpSemContext::simplify(Expr u) {
  ScopedStats _st_("opsem.simplify");

  Expr _u, _u_simp;
  _u_simp = m_z3_simplifier->simplify(u);
  _u = UseLambdas ? coerceConstArrayToLambda(_u_simp, efac()) : _u_simp;
  LOG(
      "opsem.simplify",
      if (!isOpX<LAMBDA>(_u) && !isOpX<ITE>(_u) && dagSize(_u) > 100) {
        errs() << "Term after simplification:\n" << m_z3->toSmtLib(_u) << "\n";
      });

  LOG(
      "opsem.dump.subformulae",
      if ((isOpX<EQ>(_u) || isOpX<NEG>(_u)) && dagSize(_u) > 100) {
        static unsigned cnt = 0;
        std::ofstream file("assert." + std::to_string(++cnt) + ".smt2");
        file << m_z3->toSmtLibDecls(_u) << "\n";
        file << "(assert " << m_z3->toSmtLib(_u) << ")\n";
      });
  return _u;
}

void Bv2OpSemContext::write(Expr v, Expr u) {
  if (shouldSimplify()) {
    u = simplify(u);
  }

  LOG("opsem.verbose", llvm::errs() << "W: " << *u << "\n";);
  OpSemContext::write(v, u);
}
unsigned Bv2OpSemContext::ptrSzInBits() const {
  // XXX refactoring hack
  if (!m_parent && !m_memManager)
    return 32;

  return mem().ptrSzInBits();
}

void Bv2OpSemContext::setMemManager(OpSemMemManager *man) {
  m_memManager.reset(man);

  // TODO: move into MemManager
  expr::mpz_class val;
  switch (ptrSzInBits()) {
  case 64:
    // TODO: take alignment into account
    val = expr::mpz_class(0x000000000FFFFFFFU);
    break;
  case 32:
    // TODO: take alignment into account
    val = expr::mpz_class(0x0FFFFFFFU);
    break;
  default:
    LOG("opsem",
        errs() << "Unsupported pointer size: " << ptrSzInBits() << "\n";);
    llvm_unreachable("Unexpected pointer size");
  }
}

Expr Bv2OpSemContext::loadValueFromMem(Expr ptr, const llvm::Type &ty,
                                       uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  Expr res;
  if (isMemScalar())
    res = read(getMemReadRegister());
  else if (ptr) {
    auto mem = read(getMemReadRegister());
    return m_memManager->loadValueFromMem(ptr, mem, ty, align);
  }
  return res;
}

Expr Bv2OpSemContext::storeValueToMem(Expr val, Expr ptr, const llvm::Type &ty,
                                      uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  assert(getMemWriteRegister());

  Expr res;
  if (val && isMemScalar()) {
    res = val;
    write(getMemWriteRegister(), res);
  } else if (val && ptr) {
    Expr inMem = read(getMemReadRegister());
    res = m_memManager->storeValueToMem(val, ptr, inMem, ty, align);
    write(getMemWriteRegister(), res);
  }
  return res;
}

Expr Bv2OpSemContext::MemSet(Expr ptr, Expr val, unsigned len, uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  Expr mem = read(getMemReadRegister());
  Expr res = m_memManager->MemSet(ptr, val, len, mem, align);
  write(getMemWriteRegister(), res);
  return res;
}

Expr Bv2OpSemContext::MemSet(Expr ptr, Expr val, Expr len, uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  Expr mem = read(getMemReadRegister());
  Expr res = m_memManager->MemSet(ptr, val, len, mem, align);
  write(getMemWriteRegister(), res);
  return res;
}

Expr Bv2OpSemContext::MemCpy(Expr dPtr, Expr sPtr, unsigned len,
                             uint32_t align) {
  assert(m_memManager);
  assert(getMemTrsfrReadReg());
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  Expr mem = read(getMemTrsfrReadReg());
  Expr dstMemIn = read(getMemReadRegister());
  Expr res = m_memManager->MemCpy(dPtr, sPtr, len, mem, dstMemIn, align);
  if (res)
    write(getMemWriteRegister(), res);
  else {
    LOG("opsem", WARN << "memcpy with concrete length treated as noop");
  }
  return res;
}

Expr Bv2OpSemContext::MemCpy(Expr dPtr, Expr sPtr, Expr len, uint32_t align) {
  assert(m_memManager);
  assert(getMemTrsfrReadReg());
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  Expr mem = read(getMemTrsfrReadReg());
  Expr dstMemIn = read(getMemReadRegister());
  Expr res = m_memManager->MemCpy(dPtr, sPtr, len, mem, dstMemIn, align);
  if (res) {
    write(getMemWriteRegister(), res);
  } else {
    LOG("opsem", WARN << "memcpy with symbolic length treated as noop";);
  }
  return res;
}

Expr Bv2OpSemContext::MemFill(Expr dPtr, char *sPtr, unsigned len,
                              uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  Expr mem = read(getMemReadRegister());
  Expr res = m_memManager->MemFill(dPtr, sPtr, len, mem, align);
  write(getMemWriteRegister(), res);
  return res;
}

Expr Bv2OpSemContext::inttoptr(Expr intValue, const Type &intTy,
                               const Type &ptrTy) const {
  return mem().inttoptr(intValue, intTy, ptrTy);
}

Expr Bv2OpSemContext::ptrtoint(Expr ptrValue, const Type &ptrTy,
                               const Type &intTy) const {
  return mem().ptrtoint(ptrValue, ptrTy, intTy);
}

Expr Bv2OpSemContext::gep(Expr ptr, gep_type_iterator it,
                          gep_type_iterator end) const {
  return mem().gep(ptr, it, end);
}

void Bv2OpSemContext::onFunctionEntry(const Function &fn) {
  if (UseLVIInferRng)
    m_sem.runLVIAnalysis(fn);
  mem().onFunctionEntry(fn);
}
void Bv2OpSemContext::onModuleEntry(const Module &M) {
  return mem().onModuleEntry(M);
}

void Bv2OpSemContext::onBasicBlockEntry(const BasicBlock &bb) {
  if (!m_func)
    m_func = bb.getParent();
  assert(m_func == bb.getParent());
  if (m_bb)
    m_prev = m_bb;
  m_bb = &bb;
  m_inst = bb.begin();
}

void Bv2OpSemContext::declareRegister(Expr v) { m_registers.insert(v); }
bool Bv2OpSemContext::isKnownRegister(Expr v) { return m_registers.count(v); }

Expr Bv2OpSemContext::mkRegister(const llvm::BasicBlock &bb) {
  if (Expr r = getRegister(bb))
    return r;
  Expr reg = bind::boolConst(mkTerm<const BasicBlock *>(&bb, efac()));
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&bb, reg));
  return reg;
}

Expr Bv2OpSemContext::mkPtrRegisterSort(const Instruction &inst) const {
  return mem().mkPtrRegisterSort(inst);
}

Expr Bv2OpSemContext::mkPtrRegisterSort(const Function &fn) const {
  return mem().mkPtrRegisterSort(fn);
}

Expr Bv2OpSemContext::mkPtrRegisterSort(const GlobalVariable &gv) const {
  return mem().mkPtrRegisterSort(gv);
}

Expr Bv2OpSemContext::mkMemRegisterSort(const Instruction &inst) const {
  return mem().mkMemRegisterSort(inst);
}

Expr Bv2OpSemContext::mkRegister(const llvm::Instruction &inst) {
  if (Expr r = getRegister(inst))
    return r;
  Expr reg;
  // everything else is mapped to a symbolic register with a
  // non-deterministic initial value
  Expr v = mkTerm<const Value *>(&inst, efac());

  // pseudo register corresponding to memory blocks
  const Value *scalar = nullptr;
  if (isShadowMem(inst, &scalar)) {
    // if memory is single cell, allocate regular register
    if (scalar) {
      assert(scalar->getType()->isPointerTy());
      Type &eTy = *cast<PointerType>(scalar->getType())->getElementType();
      // -- create a constant with the name v[scalar]
      if (eTy.isPointerTy()) {
        reg = bind::mkConst(
            op::array::select(v, mkTerm<const Value *>(scalar, efac())),
            mem().ptrSort());
      } else {
        reg = bind::mkConst(
            op::array::select(v, mkTerm<const Value *>(scalar, efac())),
            alu().intTy(m_sem.sizeInBits(eTy)));
      }
    }

    // if tracking memory content, create array-valued register for
    // the pseudo-assignment
    else { //(true /*m_trackLvl >= MEM*/) {
      reg = bind::mkConst(v, mkMemRegisterSort(inst));
    }
  } else {
    const Type &ty = *inst.getType();
    switch (ty.getTypeID()) {
    case Type::IntegerTyID:
    case Type::StructTyID:      // treat aggregate types in register as int
    case Type::FixedVectorTyID: // treat fixed vectors in registers as int
      reg = bind::mkConst(v, alu().intTy(m_sem.sizeInBits(ty)));
      break;
    case Type::PointerTyID:
      reg = bind::mkConst(v, mkPtrRegisterSort(inst));
      break;
    default:
      ERR << "unhandled type: " << ty << " of " << inst << "\n";
      llvm_unreachable(nullptr);
    }
  }
  assert(reg);
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&inst, reg));
  return reg;
}

Expr Bv2OpSemContext::mkRegister(const llvm::Function &fn) {
  if (Expr r = getRegister(fn))
    return r;

  Expr reg;
  Expr v = mkTerm<const Value *>(&fn, efac());

  reg = bind::mkConst(v, mkPtrRegisterSort(fn));
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&fn, reg));
  return reg;
}

Expr Bv2OpSemContext::mkRegister(const llvm::GlobalVariable &gv) {
  if (Expr r = getRegister(gv))
    return r;
  Expr reg;
  Expr v = mkTerm<const Value *>(&gv, efac());

  reg = bind::mkConst(v, mkPtrRegisterSort(gv));
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&gv, reg));
  return reg;
}

Expr Bv2OpSemContext::mkRegister(const llvm::Value &v) {
  if (auto const *bb = dyn_cast<llvm::BasicBlock>(&v)) {
    return mkRegister(*bb);
  }
  if (auto const *inst = dyn_cast<llvm::Instruction>(&v)) {
    return mkRegister(*inst);
  }
  if (auto const *fn = dyn_cast<llvm::Function>(&v)) {
    return mkRegister(*fn);
  }
  if (auto const *gv = dyn_cast<llvm::GlobalVariable>(&v)) {
    return mkRegister(*gv);
  }
  ERR << "cannot make symbolic register for " << v << "\n";
  llvm_unreachable(nullptr);
}

Expr Bv2OpSemContext::getConstantValue(const llvm::Constant &c) {
  // -- easy common cases
  if (false && isa<const UndefValue>(c)) {
    // XXX causes issues with structures, disable for now
    // -- `undef` is an arbitrary bit-pattern, so we treat it as 0
    return alu().ui(0U, m_sem.sizeInBits(c));
  } else if (isa<ConstantPointerNull>(c) ||
             (c.getType()->isPointerTy() && isa<UndefValue>(c))) {
    return mem().nullPtr();
  } else if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&c)) {
    if (ci->getType()->isIntegerTy(1))
      return ci->isOne() ? alu().ui(1U, 1) : alu().ui(0U, 1);
    else if (ci->isZero())
      return alu().ui(0U, m_sem.sizeInBits(c));
    else if (ci->isOne())
      return alu().ui(1U, m_sem.sizeInBits(c));

    expr::mpz_class k = toMpz(ci->getValue());
    return alu().num(k, m_sem.sizeInBits(c));
  }

  if (c.getType()->isIntegerTy()) {
    ConstantExprEvaluator ce(m_sem.getDataLayout());
    auto GVO = ce.evaluate(&c);
    if (GVO.hasValue()) {
      GenericValue gv = GVO.getValue();
      expr::mpz_class k = toMpz(gv.IntVal);
      return alu().num(k, m_sem.sizeInBits(c));
    }
  } else if (c.getType()->isVectorTy()) {
    ConstantExprEvaluator ce(m_sem.getDataLayout());
    ce.setContext(*this);
    auto GVO = ce.evaluate(&c);
    if (GVO.hasValue()) {
      auto &gv = GVO.getValue();
      if (!gv.AggregateVal.empty()) {
        auto vecBv0 = m_sem.vec(c.getType(), gv.AggregateVal, *this);
        if (vecBv0.hasValue()) {
          const APInt &vecBv = vecBv0.getValue();
          expr::mpz_class k = toMpz(vecBv);
          return alu().num(k, vecBv.getBitWidth());
        }
      }
    }
    LOG("opsem", WARN << "unhandled constant vector" << c;);
  } else if (c.getType()->isStructTy()) {
    ConstantExprEvaluator ce(m_sem.getDataLayout());
    ce.setContext(*this);
    auto GVO = ce.evaluate(&c);
    if (GVO.hasValue()) {
      GenericValue &gv = GVO.getValue();
      if (!gv.AggregateVal.empty()) {
        auto aggBvO = m_sem.agg(c.getType(), gv.AggregateVal, *this);
        if (aggBvO.hasValue()) {
          const APInt &aggBv = aggBvO.getValue();
          expr::mpz_class k = toMpz(aggBv);
          return alu().num(k, aggBv.getBitWidth());
        }
      }
    }
    LOG("opsem", WARN << "unhandled constant struct " << c;);
  } else if (c.getType()->isPointerTy()) {
    LOG("opsem", WARN << "unhandled constant pointer " << c;);
  } else {
    LOG("opsem", WARN << "unhandled constant " << c;);
  }
  return Expr();
}

std::pair<char *, unsigned>
Bv2OpSemContext::getGlobalVariableInitValue(const llvm::GlobalVariable &gv) {
  return m_memManager->getGlobalVariableInitValue(gv);
}

void Bv2OpSemContext::resetSolver() {
  m_z3_solver->reset();
  m_addedToSolver.clear();
}

void Bv2OpSemContext::addToSolver(const Expr e) {
  if (!m_addedToSolver.count(e)) {
    // if not found, add to solver and keep track
    m_z3_solver->assertExpr(e);
    m_addedToSolver.insert(e);
  }
}

void Bv2OpSemContext::toSmtLib(llvm::raw_ostream &o) {
  m_z3_solver->toSmtLib(o);
}

boost::tribool Bv2OpSemContext::solve() { return m_z3_solver->solve(); }

Expr Bv2OpSemContext::ptrToAddr(Expr p) { return mem().ptrToAddr(p); }

Expr Bv2OpSemContext::getRawMem(Expr p) { return mem().getRawMem(p); }

} // namespace details

Bv2OpSem::Bv2OpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
                   TrackLevel trackLvl)
    : OperationalSemantics(efac), m_pass(pass), m_trackLvl(trackLvl),
      m_td(&dl) {
  m_canFail = pass.getAnalysisIfAvailable<CanFail>();
  m_lvi_map = UseLVIInferRng ? std::make_unique<lvi_func_map_t>() : nullptr;
  auto *p = pass.getAnalysisIfAvailable<TargetLibraryInfoWrapperPass>();
  if (p)
    m_tliWrapper = p;

  // -- hack to get ENode::dump() to compile by forcing a use
  LOG("dump.debug", trueE->dump(););
}

OpSemContextPtr Bv2OpSem::mkContext(SymStore &values, ExprVector &side) {
  return OpSemContextPtr(
      new seahorn::details::Bv2OpSemContext(*this, values, side));
}

Bv2OpSem::Bv2OpSem(const Bv2OpSem &o)
    : OperationalSemantics(o), m_pass(o.m_pass), m_trackLvl(o.m_trackLvl),
      m_td(o.m_td), m_canFail(o.m_canFail) {}

Expr Bv2OpSem::errorFlag(const BasicBlock &BB) {
  // -- if BB belongs to a function that cannot fail, errorFlag is always false
  if (m_canFail && !m_canFail->canFail(BB.getParent()))
    return falseE;
  return this->OperationalSemantics::errorFlag(BB);
}

Bv2OpSem::~Bv2OpSem() = default;

void Bv2OpSem::exec(const BasicBlock &bb,
                    seahorn::details::Bv2OpSemContext &ctx) {
  ctx.onBasicBlockEntry(bb);

  seahorn::details::OpSemVisitor v(ctx, *this);
  v.visitBasicBlock(const_cast<BasicBlock &>(bb));
  // skip PHI instructions
  for (; isa<PHINode>(ctx.getCurrentInst()); ++ctx)
    ;

  while (intraStep(ctx)) {
    /* do nothing */;
  }
}

void Bv2OpSem::execPhi(const BasicBlock &bb, const BasicBlock &from,
                       seahorn::details::Bv2OpSemContext &ctx) {
  ctx.onBasicBlockEntry(bb);
  ctx.setPrevBb(from);
  intraPhi(ctx);
}

Expr Bv2OpSem::symbolicIndexedOffset(gep_type_iterator TI, gep_type_iterator TE,
                                     seahorn::details::Bv2OpSemContext &ctx) {
  unsigned ptrSz = pointerSizeInBits();

  // numeric offset
  uint64_t noffset = 0;
  // symbolic offset
  Expr soffset;

  for (; TI != TE; ++TI) {
    Value *CurVal = TI.getOperand();
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
        soffset = (soffset ? mk<BADD>(soffset, a) : a);
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

Expr Bv2OpSem::getOperandValue(const Value &v,
                               seahorn::details::Bv2OpSemContext &ctx) {
  Expr res;
  if (auto *bb = dyn_cast<BasicBlock>(&v)) {
    Expr reg = ctx.getRegister(*bb);
    if (reg)
      res = ctx.read(reg);
  } else if (auto *fn = dyn_cast<Function>(&v)) {
    if (Expr reg = ctx.getRegister(*fn)) {
      res = ctx.read(reg);
    } else
      res = ctx.getConstantValue(*fn);
  } else if (auto *gv = dyn_cast<GlobalVariable>(&v)) {
    if (Expr reg = ctx.getRegister(*gv)) {
      res = ctx.read(reg);
    } else
      res = ctx.getConstantValue(*gv);
  } else if (auto *ce = dyn_cast<ConstantExpr>(&v)) {
    // HACK: handle bitcast of a global variable
    if (ce->getType()->isPointerTy() &&
        ce->getOpcode() == Instruction::BitCast) {
      if (auto *gv = dyn_cast<GlobalVariable>(ce->getOperand(0))) {
        if (Expr reg = ctx.getRegister(*gv))
          res = ctx.read(reg);
      }
    }
    if (!res) {
      res = ctx.getConstantValue(*ce);
      LOG("opsem",
          if (!res) WARN << "Failed to evaluate constant expression " << v;);
    }
  } else if (auto *cv = dyn_cast<Constant>(&v)) {
    res = ctx.getConstantValue(*cv);
    LOG("opsem", if (!res) WARN << "Failed to evaluate a constant " << v;);
  } else {
    Expr reg = ctx.getRegister(v);
    if (reg)
      res = ctx.read(reg);
    else
      WARN << "Failed to get register for: " << v << "\n";
  }
  return res;
}

bool Bv2OpSem::isSymReg(Expr v, seahorn::details::Bv2OpSemContext &C) {
  if (this->OperationalSemantics::isSymReg(v))
    return true;

  if (C.isKnownRegister(v))
    return true;

  // TODO: memStart and memEnd

  // a symbolic register is any expression that resolves to an
  // llvm::Value XXX it might be better to register registers with a
  // SymStore and XXX let register be only expressions that are
  // explicitly marked as registers
  if (!isOpX<FAPP>(v))
    return false;

  Expr u = bind::fname(v);
  u = bind::fname(u);
  if (isOpX<VALUE>(u))
    return true;

  errs() << "Unexpected symbolic value: " << *v << "\n";
  llvm_unreachable("unexpected");
}

const Value &Bv2OpSem::conc(Expr v) const {
  assert(isOpX<FAPP>(v));
  // name of the app
  Expr u = bind::fname(v);
  // name of the fdecl
  u = bind::fname(u);
  assert(isOpX<VALUE>(v));
  return *getTerm<const Value *>(v);
}

bool Bv2OpSem::isSkipped(const Value &v) const {
  if (!OperationalSemantics::isTracked(v))
    return true;
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
    ERR << "Unexpected label type";
    llvm_unreachable(nullptr);
  case Type::MetadataTyID:
    ERR << "Unexpected metadata type";
    llvm_unreachable(nullptr);
  case Type::X86_MMXTyID:
    LOG("opsem", WARN << "Unsupported X86 type\n");
    return true;
  case Type::TokenTyID:
    llvm_unreachable("Unexpected token type");
  case Type::IntegerTyID:
    return false;
  case Type::FunctionTyID:
    llvm_unreachable("Unexpected function type");
  case Type::StructTyID:
    return false;
  case Type::ArrayTyID:
    LOG("opsem", WARN << "Unsupported array type\n";);
    return true;
  case Type::PointerTyID:
    // -- pointers are handled earlier in the procedure
    llvm_unreachable(nullptr);
  case Type::FixedVectorTyID:
    return false;
  case Type::ScalableVectorTyID:
    LOG("opsem", WARN << "Unsupported vector type\n";);
    return true;
  default:
    LOG("opsem", ERR << "Unknown type: " << *ty << "\n";);
    llvm_unreachable(nullptr);
  }
  llvm_unreachable(nullptr);
}

/// \brief Executes one intra-procedural instructions in the current
/// context. Returns false if there are no more instructions to
/// execute after the last one
bool Bv2OpSem::intraStep(seahorn::details::Bv2OpSemContext &C) {
  if (C.isAtBbEnd())
    return false;

  // -- repeat flag can be set during intraStep and must be reset at the end
  assert(!C.isRepeatInstruction());
  const Instruction &inst = C.getCurrentInst();

  // -- non-branch terminators are executed elsewhere
  if (inst.isTerminator() && !isa<BranchInst>(&inst))
    return false;

  // -- either skip or execute the instruction
  if (isSkipped(inst)) {
    skipInst(inst, C);
  } else {
    // -- execute instruction
    seahorn::details::OpSemVisitor v(C, *this);
    LOG("opsem.verbose", errs() << "Executing: " << inst << "\n";);
    v.visit(const_cast<Instruction &>(inst));
  }

  // -- advance instruction pointer if needed
  if (C.isRepeatInstruction()) {
    C.resetRepeatInstruction();
    return true;
  }

  if (!inst.isTerminator()) {
    ++C;
    return true;
  }
  return false;
}

void Bv2OpSem::intraPhi(seahorn::details::Bv2OpSemContext &C) {
  assert(C.getPrevBb());

  // act is ignored since phi node only introduces a definition
  seahorn::details::OpSemPhiVisitor v(C, *this);
  v.visitBasicBlock(const_cast<BasicBlock &>(*C.getCurrBb()));
}
/// \brief Executes one intra-procedural branch instruction in the
/// current context. Assumes that current instruction is a branch
void Bv2OpSem::intraBr(seahorn::details::Bv2OpSemContext &C,
                       const BasicBlock &dst) {
  const BranchInst *br = dyn_cast<const BranchInst>(&C.getCurrentInst());
  if (!br)
    return;

  // next instruction
  ++C;

  if (br->isConditional()) {
    const Value &c = *br->getCondition();
    if (const Constant *cv = dyn_cast<const Constant>(&c)) {
      ConstantExprEvaluator ce(getDataLayout());
      auto gv = ce.evaluate(cv);
      assert(gv.hasValue());
      if ((gv->IntVal.isOneValue() && br->getSuccessor(0) != &dst) ||
          (gv->IntVal.isNullValue() && br->getSuccessor(1) != &dst)) {
        C.resetSide();
        C.addScopedSide(C.read(errorFlag(*C.getCurrBb())));
      }
    } else if (Expr target = getOperandValue(c, C)) {
      Expr cond = br->getSuccessor(0) == &dst ? target : mk<NEG>(target);
      cond = boolop::lor(C.read(errorFlag(*C.getCurrBb())), cond);
      C.addScopedSide(cond);
      C.onBasicBlockEntry(dst);
    }
  } else {
    if (br->getSuccessor(0) != &dst) {
      C.resetSide();
      C.addScopedSide(C.read(errorFlag(*C.getCurrBb())));
    } else {
      C.onBasicBlockEntry(dst);
    }
  }
}

void Bv2OpSem::skipInst(const Instruction &inst,
                        seahorn::details::Bv2OpSemContext &ctx) {
  const Value *s;
  if (isShadowMem(inst, &s))
    return;
  if (ctx.isIgnored(inst))
    return;
  if (!OperationalSemantics::isTracked(inst))
    // silently ignore instructions that are filtered out
    return;
  ctx.ignore(inst);
  LOG("opsem", WARN << "skipping instruction: " << inst << " @ "
                    << inst.getParent()->getName() << " in "
                    << inst.getParent()->getParent()->getName(););
}

void Bv2OpSem::unhandledValue(const Value &v,
                              seahorn::details::Bv2OpSemContext &ctx) {
  if (const Instruction *inst = dyn_cast<const Instruction>(&v))
    return unhandledInst(*inst, ctx);
  LOG("opsem", WARN << "unhandled value: " << v;);
}
void Bv2OpSem::unhandledInst(const Instruction &inst,
                             seahorn::details::Bv2OpSemContext &ctx) {
  llvm::SmallString<1024> msg;
  llvm::raw_svector_ostream out(msg);
  if (ctx.isIgnored(inst))
    return;
  ctx.ignore(inst);
  out << "unhandled instruction: " << inst << " @ "
      << inst.getParent()->getName() << " in "
      << inst.getParent()->getParent()->getName() << " ";
  auto dloc = inst.getDebugLoc();
  if (dloc) {
    out << dloc->getFilename() << ":" << dloc->getLine() << "]";
  }
  LOG("opsem", WARN << out.str());
}

/// \brief Returns a symbolic register corresponding to a value
Expr Bv2OpSem::mkSymbReg(const Value &v, OpSemContext &_ctx) {
  return seahorn::details::ctx(_ctx).mkRegister(v);
}

Expr Bv2OpSem::getSymbReg(const Value &v, const OpSemContext &_ctx) const {
  return const_ctx(_ctx).getRegister(v);
}

void Bv2OpSem::execEdg(const BasicBlock &src, const BasicBlock &dst,
                       seahorn::details::Bv2OpSemContext &ctx) {
  exec(src, ctx.pc(trueE));
  execBr(src, dst, ctx);
  execPhi(dst, src, ctx);

  // an edge into a basic block that does not return includes the block itself
  const auto *term = dst.getTerminator();
  if (term && isa<const UnreachableInst>(term))
    exec(dst, ctx);
}

void Bv2OpSem::execBr(const BasicBlock &src, const BasicBlock &dst,
                      seahorn::details::Bv2OpSemContext &ctx) {
  ctx.onBasicBlockEntry(src);
  ctx.setInstruction(*src.getTerminator());
  intraBr(ctx, dst);
}

Optional<APInt> Bv2OpSem::agg(Type *aggTy,
                              const std::vector<GenericValue> &elements,
                              details::Bv2OpSemContext &ctx) {
  APInt res;
  APInt next;
  int resWidth = 0; // treat initial res as empty
  auto *STy = dyn_cast<StructType>(aggTy);
  if (!STy)
    llvm_unreachable("not supporting agg types other than struct");
  const StructLayout *SL = getDataLayout().getStructLayout(STy);
  for (size_t i = 0; i < elements.size(); i++) {
    const GenericValue element = elements[i];
    Type *ElmTy = STy->getElementType(i);
    if (element.AggregateVal.empty()) {
      // Assuming only dealing with Int or Pointer as struct terminal elements
      if (ElmTy->isIntegerTy())
        next = element.IntVal;
      else if (ElmTy->isPointerTy()) {
        auto ptrBv = reinterpret_cast<intptr_t>(GVTOP(element));
        next = APInt(getDataLayout().getTypeSizeInBits(ElmTy), ptrBv);
      } else {
        // this should be handled in constant evaluation step
        LOG("opsem", WARN << "unsupported type " << *ElmTy
                          << " to convert in aggregate.";);
        llvm_unreachable(
            "Only support converting Int or Pointer in aggregates");
        return llvm::None;
      }
    } else {
      auto AIO = agg(ElmTy, element.AggregateVal, ctx);
      if (AIO.hasValue())
        next = AIO.getValue();
      else {
        LOG("opsem", WARN << "nested struct conversion failed";);
        return llvm::None;
      }
    }
    // Add padding to element
    int elOffset = SL->getElementOffset(i);
    if (elOffset > resWidth) {
      res = res.zext(elOffset);
      resWidth = elOffset;
    }
    // lower index => LSB; higher index => MSB
    size_t combinedWidth = resWidth + next.getBitWidth();
    res = combinedWidth > res.getBitWidth() ? res.zext(combinedWidth) : res;
    next = combinedWidth > next.getBitWidth() ? next.zext(combinedWidth) : next;
    next <<= resWidth;
    res |= next;
    resWidth = res.getBitWidth();
  }
  unsigned aggSize = getDataLayout().getTypeSizeInBits(STy);
  if (res.getBitWidth() < aggSize)
    res = res.zext(aggSize); // padding for last element
  return res;
}

Optional<APInt> Bv2OpSem::vec(Type *vecTy,
                              const std::vector<GenericValue> &elements,
                              details::Bv2OpSemContext &ctx) {

  assert(vecTy->isVectorTy());
  unsigned resBits = getDataLayout().getTypeSizeInBits(vecTy);
  unsigned elemBits = getDataLayout().getTypeSizeInBits(vecTy->getScalarType());

  APInt res(resBits, 0);

  unsigned shiftBits = 0;
  for (auto &gv : elements) {
    APInt intVal = gv.IntVal.zext(resBits);
    intVal <<= shiftBits;
    res |= intVal;
    shiftBits += elemBits;
  }

  errs() << "res is " << res << "\n";
  return res;
}

void Bv2OpSem::initCrabAnalysis(const llvm::Module &M) {
  // Get seadsa -- pointer analysis
  auto &dsa_pass = m_pass.getAnalysis<seadsa::ShadowMemPass>().getShadowMem();
  auto &dsa = dsa_pass.getDsaAnalysis();

  // XXX: use of legacy operational semantics
  auto &tli = m_pass.getAnalysis<TargetLibraryInfoWrapperPass>();

  clam::SeaDsaHeapAbstractionParams params;
  params.is_context_sensitive =
      (dsa.kind() == seadsa::GlobalAnalysisKind::CONTEXT_SENSITIVE);
  params.precision_level = clam::CrabBuilderPrecision::MEM;
  std::unique_ptr<clam::HeapAbstraction> heap_abs =
      std::make_unique<clam::SeaDsaHeapAbstraction>(M, dsa, params);

  // -- Set parameters for CFG
  clam::CrabBuilderParams cfg_builder_params;
  LOG("opsem-crab", cfg_builder_params.print_cfg = true;);
  cfg_builder_params.setPrecision(clam::CrabBuilderPrecision::MEM);
  cfg_builder_params.interprocedural = true;
  if (UseCrabLowerIsDeref) {
    // Use CrabIR instrumentation for offset/size of ptr
    cfg_builder_params.add_is_deref = true;
  }
  cfg_builder_params.lowerUnsignedICmpIntoSigned();
  cfg_builder_params.lower_arithmetic_with_overflow_intrinsics = true;

  m_cfg_builder_man = std::make_unique<clam::CrabBuilderManager>(
      cfg_builder_params, tli, std::move(heap_abs));
  // -- Initialize crab for solving ranges
  m_crab_rng_solver =
      std::make_unique<clam::InterGlobalClam>(M, *m_cfg_builder_man);
}

void Bv2OpSem::runCrabAnalysis() {
  /// Set Crab parameters
  clam::AnalysisParams aparams;
  aparams.dom = CrabDom;
  aparams.run_inter = true;
  aparams.check = clam::CheckerKind::NOCHECKS;
  aparams.widening_delay = 2; // set to delay widening

  if (UseCrabCheckIsDeref) {
    crab::domains::crab_domain_params_man::get().set_param(
        "region.is_dereferenceable", "true");
  }
  /// Run the Crab analysis
  clam::ClamGlobalAnalysis::abs_dom_map_t assumptions;
  LOG("opsem-crab",
      aparams.print_invars = clam::InvariantPrinterOptions::BLOCKS;);
  Stats::resume("opsem.crab");
  m_crab_rng_solver->analyze(aparams, assumptions);
  Stats::stop("opsem.crab");
}

void Bv2OpSem::runLVIAnalysis(const Function &F) {
  if (m_lvi_map) {
    Function &fn = const_cast<Function &>(F);
    LazyValueInfoWrapperPass *m_lvi =
        &m_pass.getAnalysis<LazyValueInfoWrapperPass>(fn);
    if (m_lvi) {
      m_lvi_map->insert({&F, m_lvi});
      LOG("opsem-rng", MSG << "Running LVI on function: " << F.getName(););
    }
  }
}

const llvm::ConstantRange Bv2OpSem::getCrabInstRng(const llvm::Instruction &I) {
  unsigned IntWidth = I.getType()->getIntegerBitWidth();
  if (!m_crab_rng_solver)
    return llvm::ConstantRange::getFull(IntWidth);
  return m_crab_rng_solver->range(I);
}

const llvm::ConstantRange Bv2OpSem::getLVIInstRng(llvm::Instruction &I) {
  unsigned IntWidth = getDataLayout().getTypeSizeInBits(I.getType());
  if (m_lvi_map) {
    Function *fn = I.getFunction();
    if (fn) {
      auto it = m_lvi_map->find(fn);
      if (it != m_lvi_map->end()) {
        return it->second->getLVI().getConstantRange(dyn_cast<Value>(&I), &I);
      }
    }
  }
  return llvm::ConstantRange::getFull(IntWidth);
}

} // namespace seahorn

namespace seahorn {
namespace details {
/// \brief Unwraps a context
seahorn::details::Bv2OpSemContext &ctx(OpSemContext &_ctx) {
  return static_cast<seahorn::details::Bv2OpSemContext &>(_ctx);
}
} // namespace details
} // namespace seahorn
namespace {
// \brief Unwraps a const context
const seahorn::details::Bv2OpSemContext &const_ctx(const OpSemContext &_ctx) {
  return static_cast<const seahorn::details::Bv2OpSemContext &>(_ctx);
}
} // namespace
