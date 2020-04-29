#include "seahorn/Transforms/Scalar/LowerGvInitializers.hh"

#include "boost/format.hpp"

#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/GlobalStatus.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

static llvm::cl::opt<bool>
LowerGvStruct("lower-gv-init-struct",
              llvm::cl::desc("Lower initializers of structs"),
              llvm::cl::init(true));
namespace seahorn {
char LowerGvInitializers::ID = 0;

/// XXX: from CtorUtils.cpp
///
/// Given a llvm.global_ctors list that we can understand,
/// return a list of the functions and null terminator as a vector.
static std::vector<Function *> parseGlobalCtors(GlobalVariable *GV) {
  if (GV->getInitializer()->isNullValue())
    return std::vector<Function *>();
  ConstantArray *CA = cast<ConstantArray>(GV->getInitializer());
  std::vector<Function *> Result;
  Result.reserve(CA->getNumOperands());
  for (User::op_iterator i = CA->op_begin(), e = CA->op_end(); i != e; ++i) {
    ConstantStruct *CS = cast<ConstantStruct>(*i);
    Result.push_back(dyn_cast<Function>(CS->getOperand(1)));
  }
  return Result;
}

/// XXX: from CtorUtils.cpp
///
/// Find the llvm.global_ctors list, verifying that all initializers have an
/// init priority of 65535.
static GlobalVariable *findGlobalCtors(Module &M) {

  GlobalVariable *GV = M.getGlobalVariable("llvm.global_ctors");
  if (!GV)
    return nullptr;

  // Verify that the initializer is simple enough for us to handle. We are
  // only allowed to optimize the initializer if it is unique.
  if (!GV->hasUniqueInitializer())
    return nullptr;

  if (isa<ConstantAggregateZero>(GV->getInitializer()))
    return GV;
  ConstantArray *CA = cast<ConstantArray>(GV->getInitializer());

  for (User::op_iterator i = CA->op_begin(), e = CA->op_end(); i != e; ++i) {
    if (isa<ConstantAggregateZero>(*i))
      continue;
    ConstantStruct *CS = cast<ConstantStruct>(*i);
    if (isa<ConstantPointerNull>(CS->getOperand(1)))
      continue;

    // Must have a function or null ptr.
    if (!isa<Function>(CS->getOperand(1)))
      return nullptr;

    // Init priority must be standard.
    ConstantInt *CI = cast<ConstantInt>(CS->getOperand(0));
    if (CI->getZExtValue() != 65535)
      return nullptr;
  }
  return GV;
}

// XXX: From DummyMainFunction.cpp
static Function &makeNewNondetFn(Module &m, Type &type, unsigned num,
                                 std::string prefix) {
  std::string name;
  unsigned c = num;
  do
    name = boost::str(boost::format(prefix + "%d") % (c++));
  while (m.getNamedValue(name));
  Function *res = dyn_cast<Function>(m.getOrInsertFunction(name, &type).getCallee());
  assert(res);
  return *res;
}

/// C may have non-instruction users. Can all of those users be turned into
/// instructions?
static bool allNonInstructionUsersCanBeMadeInstructions(Constant *C) {
  // We don't do this exhaustively. The most common pattern that we really need
  // to care about is a constant GEP or constant bitcast - so just looking
  // through one single ConstantExpr.
  //
  // The set of constants that this function returns true for must be able to be
  // handled by makeAllConstantUsesInstructions.
  for (auto *U : C->users()) {
    if (isa<Instruction>(U))
      continue;
    if (!isa<ConstantExpr>(U))
      // Non instruction, non-constantexpr user; cannot convert this.
      return false;
    for (auto *UU : U->users())
      if (!isa<Instruction>(UU))
        // A constantexpr used by another constant. We don't try and recurse any
        // further but just bail out at this point.
        return false;
  }
  return true;
}

/// C may have non-instruction users, and
/// allNonInstructionUsersCanBeMadeInstructions has returned true. Convert the
/// non-instruction users to instructions.
static void makeAllConstantUsesInstructions(Constant *C) {
  SmallVector<ConstantExpr *, 4> Users;
  for (auto *U : C->users()) {
    if (isa<ConstantExpr>(U))
      Users.push_back(cast<ConstantExpr>(U));
    else
      // We should never get here; allNonInstructionUsersCanBeMadeInstructions
      // should not have returned true for C.
      assert(
          isa<Instruction>(U) &&
          "Can't transform non-constantexpr non-instruction to instruction!");
  }

  SmallVector<Value *, 4> UUsers;
  for (auto *U : Users) {
    UUsers.clear();
    for (auto *UU : U->users())
      UUsers.push_back(UU);
    for (auto *UU : UUsers) {
      Instruction *UI = cast<Instruction>(UU);
      Instruction *NewU = U->getAsInstruction();
      NewU->insertBefore(UI);
      UI->replaceUsesOfWith(U, NewU);
    }
    U->dropAllReferences();
  }
}

Constant *LowerGvInitializers::getNondetFn(Type *type, Module &M) {
  Constant *res = m_ndfn[type];
  if (!res) {
    res = &makeNewNondetFn(M, *type, m_ndfn.size(), "verifier.nondet.");
    m_ndfn[type] = res;
  }
  return res;
}

// Add instructions in main that initialize global variables.
bool LowerGvInitializers::runOnModule(Module &M) {
  const DataLayout *DL = &M.getDataLayout();

  Function *f = M.getFunction("main");
  if (!f) {
    LOG("lower-gv-init",
        errs()
            << "LowerGvInitializers: there is no main so nothing to lower\n");
    return false;
  }

  IRBuilder<> Builder(M.getContext());
  Builder.SetInsertPoint(&f->getEntryBlock(), f->getEntryBlock().begin());
  bool change = false;
  std::vector<GlobalVariable *> gvs;
  for (GlobalVariable &gv : make_range(M.global_begin(), M.global_end())) {
    if (gv.hasInitializer())
      gvs.push_back(&gv);
  }

  // Iterate over global variables
  for (GlobalVariable *gv : gvs) {
    // XXX: skip global variables used by seahorn for instrumentation
    if (gv->getName().startswith("sea_"))
      continue;

    // First we try to promote the global variable to a stack variable
    if (isa<ConstantInt>(gv->getInitializer())) {
      GlobalStatus GS;
      bool AddressTaken = GlobalStatus::analyzeGlobal(gv, GS);
      if (!AddressTaken && !GS.HasMultipleAccessingFunctions &&
          GS.AccessingFunction && GS.AccessingFunction->getName() == "main" &&
          allNonInstructionUsersCanBeMadeInstructions(gv)) {
        Type *ElemTy = gv->getType()->getElementType();
        AllocaInst *Alloca =
            Builder.CreateAlloca(ElemTy, nullptr, gv->getName());
        Builder.CreateAlignedStore(gv->getInitializer(), Alloca,
                                   DL->getABITypeAlignment(ElemTy));
        makeAllConstantUsesInstructions(gv);
        gv->replaceAllUsesWith(Alloca);
        gv->eraseFromParent();
        continue;
      }
    }

    // Otherwise we add a store instruction in the entry block of
    // main if initializer is a scalar
    PointerType *ty = dyn_cast<PointerType>(gv->getType());
    if (!ty)
      continue;
    Type *ety = ty->getElementType();

    // Only deal with scalars and simple structs for now.
    // TODO: Support other kinds of initializers.
    if (ety->isIntegerTy() || ety->isPointerTy() ||
        (LowerGvStruct && isa<ConstantStruct>(gv->getInitializer()))) {
      StoreInst *SI = Builder.CreateAlignedStore(gv->getInitializer(), gv,
                                                 DL->getABITypeAlignment(ety));
      LOG("lower-gv-init",
          errs() << "LowerGvInitializers: created a store " << *SI << "\n");
      change = true;
    } else if (ety->isStructTy())
      WARN << "not lowering an initializer for a global struct:  " << gv->getName();
  }

  // Iterate over global constructors
  if (GlobalVariable *GlobalCtors = findGlobalCtors(M)) {
    auto CtorFns = parseGlobalCtors(GlobalCtors);
    if (!CtorFns.empty())
      change = true;

    for (auto Fn : CtorFns) {
      // -- create a call with non-deterministic parameters
      SmallVector<Value *, 16> Args;
      for (auto &A : Fn->args()) {
        Constant *ndf = getNondetFn(A.getType(), M);
        Args.push_back(Builder.CreateCall(ndf));
      }
      CallInst *CI = Builder.CreateCall(Fn, Args);
      CallingConv::ID cc = Fn->getCallingConv();
      CI->setCallingConv(cc);
      LOG("lower-gv-init",
          errs() << "LowerGvInitializers: created a call " << *CI << "\n");
    }
  }

  return change;
}

    Pass *createLowerGvInitializersPass(){return new LowerGvInitializers();}
} // namespace seahorn

static llvm::RegisterPass<seahorn::LowerGvInitializers>
    X("lower-gv-init", "Lower initialization of global variables");
