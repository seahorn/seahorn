/*
 * Insert Taint Tracking Logic.

 * Limitation: XXX.
 */

#include "seahorn/Transforms/Instrumentation/TaintLogic.hh"

#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"

#include "llvm/CodeGen/MachineDominators.h"

#include "avy/AvyDebug.h"

#define DEBUG_TAINT 1

static llvm::cl::opt<bool> HasErrorFunc(
    "taint-logic-has-error-function",
    llvm::cl::desc("Available verifier.error function to denote error."),
    llvm::cl::init(true));

namespace seahorn {
using namespace llvm;

char TaintLogic::ID = 0;

BasicBlock *TaintLogic::createErrorBlock(Function &F, IRBuilder<> B,
                                         AllocaInst *taintVar) {
  BasicBlock *errBB = BasicBlock::Create(
      B.getContext(), "TaintCheck_" + taintVar->getName().str(), &F);

  B.SetInsertPoint(errBB);
  CallInst *CI = B.CreateCall(m_errorFn);
  B.CreateUnreachable();

  // update call graph
  if (m_CG) {
    auto f1 = m_CG->getOrInsertFunction(&F);
    auto f2 = m_CG->getOrInsertFunction(m_errorFn);
    f1->addCalledFunction(CallSite(CI), f2);
  }
  return errBB;
}

void TaintLogic::insertTaintCheck(Function &F, IRBuilder<> &B,
                                  Instruction &inst, Value *taintVar) {

  // Create error blocks
  LLVMContext &ctx = B.getContext();
  BasicBlock *err_taint_bb = BasicBlock::Create(ctx, "taint_error_bb", &F);

  B.SetInsertPoint(err_taint_bb);
  CallInst *ci_taint = B.CreateCall(m_errorFn);
  ci_taint->setDebugLoc(inst.getDebugLoc());
  B.CreateUnreachable();

  B.SetInsertPoint(&inst);

  BasicBlock *OldBB0 = inst.getParent();
  BasicBlock *Cont0 = OldBB0->splitBasicBlock(B.GetInsertPoint());
  OldBB0->getTerminator()->eraseFromParent();
  BranchInst::Create(Cont0, OldBB0);

  B.SetInsertPoint(Cont0->getFirstNonPHI());

  /// --- Taint: add check var_taint == false
  Value *taintCheck =
      B.CreateICmpEQ(B.CreateAlignedLoad(taintVar, 1),
                     ConstantInt::get(m_BoolTy, 0), "taint_check");

  BasicBlock *OldBB1 = Cont0;
  BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint());
  OldBB1->getTerminator()->eraseFromParent();
  BranchInst::Create(Cont1, err_taint_bb, taintCheck, OldBB1);

  m_TaintChecksAdded++;
}

Value *TaintLogic::allocaForValue(IRBuilder<> &B, const Value *v,
                                  uint64_t size) {
  auto it = m_inst_to_shadow.find(v);
  if (it != m_inst_to_shadow.end())
    return it->second;

  std::string name = v->getName().str() + "_taint";
  Type *t = (size == 0) ? m_BoolTy : ArrayType::get(m_BoolTy, size);
  AllocaInst *a = B.CreateAlloca(t, 0, name);
  a->setAlignment(1);
  m_inst_to_shadow[v] = a;
  return a;
}

bool TaintLogic::isTaintVarExists(const Value *val) {
  if (isa<GetElementPtrInst>(val)) {
    const GetElementPtrInst &gep =
        dynamic_cast<const GetElementPtrInst &>(*val);
    unsigned size = gep.getNumOperands();
    for (unsigned i = 0; i < size; i++) {
      auto it = m_inst_to_shadow.find(gep.getOperand(i));
      if (it != m_inst_to_shadow.end())
        return true;
    }
  } else {
    if (m_inst_to_shadow.find(val) != m_inst_to_shadow.end())
      return true;
  }
  return false;
}

Value *TaintLogic::getShadowTaintVar(IRBuilder<> &B, Value *val) {
  Value *taintVar = NULL;
  if (isa<GetElementPtrInst>(val)) {
    taintVar = getShadowTaintForGEP(B, val);
  } else {
    if (isa<BitCastInst>(val))
      val = dynamic_cast<const BitCastInst *>(val)->getOperand(0);
    if (m_inst_to_shadow.find(val) != m_inst_to_shadow.end())
      taintVar = m_inst_to_shadow[val];
  }

  return taintVar;
}

Value *TaintLogic::addShadowTaintVar(IRBuilder<> &B, Value *var,
                                     uint64_t size) {
  if (isa<BitCastInst>(*var))
    var = dynamic_cast<BitCastInst *>(var)->getOperand(0);

  auto it = m_inst_to_shadow.find(var);
  if (it != m_inst_to_shadow.end())
    return it->second;

  B.SetInsertPoint(&*m_topBB->getFirstInsertionPt());
  Value *a = allocaForValue(B, var, size);
  if (size == 0)
    B.CreateAlignedStore(ConstantInt::get(m_BoolTy, 0), a, 1);
  else {
    for (uint64_t i = 0; i < size; i++) {
      Value *indices[] = {
          0, ConstantInt::get(Type::getInt32Ty(B.getContext()), i)};
      Value *v = B.CreateConstGEP2_32(ArrayType::get(m_BoolTy, size), a, 0, i);
      B.CreateAlignedStore(ConstantInt::get(m_BoolTy, 0), v, 1);
    }
  }
  m_shadows.push_back(a);
  return a;
}

bool TaintLogic::isTaintLogicRequired(Instruction &inst) {
  if (isa<CallInst>(inst))
    return false;

  // if (m_inst_to_shadow.find(&inst) != m_inst_to_shadow.end())
  //    return true;

  BasicBlock *bb = inst.getParent();
  auto bbTaint = m_inst_to_shadow.find(bb);
  if (bbTaint != m_inst_to_shadow.end()) {
    if (isa<BranchInst>(inst) &&
        dynamic_cast<BranchInst &>(inst).isUnconditional()) {
      BasicBlock *origin = m_taint_to_bb[bbTaint->second];
      m_dm.recalculate(*inst.getParent()->getParent());
      if (m_dm.dominates((BasicBlock *)inst.getOperand(0), origin)) {
        return false;
      } else {
        return true;
      }
    } else if (!isa<LoadInst>(inst))
      return true;
  }

  bool bTaint = false;
  if (isa<PHINode>(inst)) {
    PHINode &phi = dynamic_cast<PHINode &>(inst);
    unsigned size = phi.getNumIncomingValues();
    for (unsigned i = 0; i < size && !bTaint; i++) {
      if (m_inst_to_shadow.find(phi.getIncomingValue(i)) !=
          m_inst_to_shadow.end())
        bTaint = true;
    }
  } else if (isa<BranchInst>(inst)) {
    BranchInst &branchInst = dynamic_cast<BranchInst &>(inst);
    if (branchInst.isUnconditional())
      bTaint = false;
    else
      bTaint = isTaintVarExists(branchInst.getOperand(0));
  } else {
    unsigned size = inst.getNumOperands();
    for (unsigned i = 0; i < size && !bTaint; i++) {
      const Value *op = inst.getOperand(i);
      if (isa<StoreInst>(inst)) {
        if (i <= 1 && isTaintVarExists(op))
          bTaint = true;
      } else if (isTaintVarExists(op)) {
        bTaint = true;
      }
    }
  }

  return bTaint;
}

Value *TaintLogic::getOrCreateShadowForInst(IRBuilder<> &B, Instruction &inst) {
  Value *shadow = NULL;
  auto it = m_inst_to_shadow.end();
  if (isa<StoreInst>(inst)) {
    Value *dst = inst.getOperand(1);
    if (isa<GetElementPtrInst>(dst)) {
      shadow = createShadowTaintForGEP(B, dst);
      /*GetElementPtrInst& gep = dynamic_cast<GetElementPtrInst&>(*dst);
      Value *ptr = gep.getPointerOperand();
      it = m_inst_to_shadow.find(ptr);
      if (it == m_inst_to_shadow.end()) {
          Type *t =
      ((PointerType*)gep.getPointerOperandType())->getElementType(); shadow =
      addShadowTaintVar(B, ptr, ((ArrayType*)t)->getNumElements());
      }
      else
          shadow = it->second;
      */
    } else {
      it = m_inst_to_shadow.find(dst);
      if (it == m_inst_to_shadow.end())
        shadow = addShadowTaintVar(B, dst);
      else
        shadow = it->second;
    }
  } else if (isa<BranchInst>(inst)) {
    BranchInst &branchInst = dynamic_cast<BranchInst &>(inst);
    if (branchInst.isConditional()) {
      Value *cond = branchInst.getOperand(0);
      Value *br1 = branchInst.getOperand(1);
      Value *br2 = branchInst.getOperand(2);
      it = m_inst_to_shadow.find(cond);
      if (it == m_inst_to_shadow.end()) {
        shadow = getOrCreateShadowForInst(B, *((Instruction *)cond));
      }
      // assert (it != m_inst_to_shadow.end());
      else {
        shadow = it->second;
      }
      m_dm.recalculate(*inst.getParent()->getParent());
      if (!m_dm.dominates((BasicBlock *)br1, inst.getParent()))
        m_inst_to_shadow[br1] = shadow;
      if (!m_dm.dominates((BasicBlock *)br2, inst.getParent()))
        m_inst_to_shadow[br2] = shadow;
      m_taint_to_bb[shadow] = inst.getParent();
    } else {
      Value *parent = branchInst.getParent();
      Value *br = branchInst.getOperand(0);
      it = m_inst_to_shadow.find(parent);
      assert(it != m_inst_to_shadow.end());
      shadow = it->second;
      auto origin = m_taint_to_bb.find(it->second);
      assert(origin != m_taint_to_bb.end());
      if (origin == m_taint_to_bb.end() || origin->second != br)
        m_inst_to_shadow[br] = shadow;
    }
  } else if (isa<GetElementPtrInst>(inst)) {
    GetElementPtrInst &gep = dynamic_cast<GetElementPtrInst &>(inst);
    Value *ptr = gep.getPointerOperand();
    it = m_inst_to_shadow.find(ptr);
    if (it == m_inst_to_shadow.end()) {
      Type *t = ((PointerType *)gep.getPointerOperandType())->getElementType();
      unsigned eSize = 0;
      if (t->isArrayTy()) {
        eSize = ((ArrayType *)t)->getNumElements();
      } else if (t->isStructTy()) {
        eSize = ((StructType *)t)->getNumElements();
      }
      shadow = addShadowTaintVar(B, ptr, eSize);
    } else
      shadow = it->second;
  } else {
    it = m_inst_to_shadow.find(&inst);
    if (it == m_inst_to_shadow.end())
      shadow = addShadowTaintVar(B, &inst);
    else
      shadow = it->second;
  }

  return shadow;
}

void TaintLogic::addAllShadowTaintVars(IRBuilder<> &B,
                                       std::vector<Instruction *> &WorkList) {
  B.SetInsertPoint(&*m_topBB->getFirstInsertionPt());
  for (Instruction *I : WorkList) {
    if (isa<CallInst>(I)) {
      unsigned operands = I->getNumOperands();
      StringRef funcName = I->getOperand(operands - 1)->getName();
      if (funcName.compare("ifc_set_secret") == 0) {
        Value *var = I->getOperand(0);
        Value *a = addShadowTaintVar(B, var);
        B.SetInsertPoint(I->getNextNode());
        B.CreateAlignedStore(ConstantInt::get(m_BoolTy, 1), a, 1);
      }
      continue;
    }

    if (isTaintLogicRequired(*I) == false)
      continue;

    getOrCreateShadowForInst(B, *I);
  }
}

void TaintLogic::insertTaintLogic(IRBuilder<> &B, Instruction &inst) {
  if (isTaintLogicRequired(inst) == false)
    return;

  Instruction *insertPoint =
      (isa<TerminatorInst>(inst)) ? &inst : inst.getNextNode();
  if (isa<PHINode>(inst))
    insertPoint = inst.getParent()->getFirstNonPHI();
  B.SetInsertPoint(insertPoint);

  // First capture shadow operands
  std::vector<Value *> shadows;
  unsigned size = inst.getNumOperands();
  for (unsigned i = 0; i < size; i++) {
    Value *shadow = NULL;
    if (isa<StoreInst>(inst) && i == 1)
      continue;
    else if (isa<GetElementPtrInst>(inst) &&
             dynamic_cast<GetElementPtrInst &>(inst).getPointerOperandIndex() ==
                 i) {
      shadow = getShadowTaintVar(B, &inst);
    } else if ((isa<SelectInst>(inst) || isa<BranchInst>(inst)) && i > 0) {
      continue;
    } else {
      Value *op = inst.getOperand(i);
      shadow = getShadowTaintVar(B, op);
    }

    if (shadow != NULL)
      shadows.push_back(shadow);
  }

  BasicBlock *bb = inst.getParent();
  auto bbTaint = m_inst_to_shadow.find(bb);
  if (isa<BranchInst>(inst)) {
    BranchInst &branchInst = dynamic_cast<BranchInst &>(inst);
    if (branchInst.isUnconditional() && bbTaint != m_inst_to_shadow.end()) {
      m_inst_to_shadow[branchInst.getOperand(0)] = bbTaint->second;
      return;
    }
  }

  if (bbTaint != m_inst_to_shadow.end())
    shadows.push_back(bbTaint->second);

  if (isa<GetElementPtrInst>(inst) && shadows.size() == 1 &&
      isa<GetElementPtrInst>(shadows[0]))
    return;

  size = shadows.size();
  unsigned numElements = (size == 0) ? 1 : getNumTaintElements(shadows[0]);
  Value *taint[numElements];
  for (unsigned e = 0; e < numElements; e++) {
    taint[e] = (size == 0) ? (Value *)ConstantInt::get(m_BoolTy, 0)
                           : createLoadTaint(B, shadows[0], e);
    for (unsigned i = 1; i < size; i++) {
      Value *tmp = B.CreateAlignedLoad(shadows[i], 1);
      taint[e] = B.CreateOr(taint[e], tmp,
                            inst.getName() + "_" + std::to_string(e) + "_" +
                                std::to_string(i));
    }
  }

  if (isa<SelectInst>(inst)) {
    assert(numElements == 1 &&
           "No support for more than 1 for SelectInst - for now\n");
    Value *shadow1 = getShadowTaintVar(B, inst.getOperand(1));
    if (shadow1 == nullptr)
      shadow1 = (Value *)ConstantInt::get(m_BoolTy, 0);
    else
      shadow1 = B.CreateAlignedLoad(shadow1, 1);
    Value *shadow2 = getShadowTaintVar(B, inst.getOperand(2));
    if (shadow2 == nullptr)
      shadow2 = (Value *)ConstantInt::get(m_BoolTy, 0);
    else
      shadow2 = B.CreateAlignedLoad(shadow2, 1);

    Value *shadowSel = B.CreateSelect(inst.getOperand(0), shadow1, shadow2);
    taint[0] = B.CreateOr(taint[0], shadowSel);
  }

  Value *a = getOrCreateShadowForInst(B, inst);
  if (isa<StoreInst>(inst)) {
    Value *dst = inst.getOperand(1);
    if (isa<GetElementPtrInst>(dst)) {
      a = getShadowTaintForGEP(B, dst);
    }
  } else if (isa<GetElementPtrInst>(inst)) {
    a = getShadowTaintForGEP(B, &inst);
  } else if (!isa<BranchInst>(inst))
    a = getShadowTaintVar(B, &inst);

  if (!isa<BranchInst>(inst)) {
    B.SetInsertPoint(insertPoint);
    assert(getNumTaintElements(a) == numElements);
    if (a->getType()->isPointerTy() &&
        (((PointerType *)a->getType())->getElementType()->isArrayTy() ||
         ((PointerType *)a->getType())->getElementType()->isStructTy())) {
      for (unsigned e = 0; e < numElements; e++) {
        Value *g = B.CreateConstGEP2_32(ArrayType::get(m_BoolTy, numElements),
                                        a, 0, e);
        B.CreateAlignedStore(taint[e], g, 1);
      }
    } else
      B.CreateAlignedStore(taint[0], a, 1);
  } else {
    BranchInst &branchInst = dynamic_cast<BranchInst &>(inst);
    assert(branchInst.isConditional());
    Value *br1 = inst.getOperand(1);
    Value *br2 = inst.getOperand(2);

    a = m_inst_to_shadow[inst.getOperand(0)];
    B.CreateAlignedStore(taint[0], a, 1);

    m_dm.recalculate(*inst.getParent()->getParent());
    if (!m_dm.dominates((BasicBlock *)br1, inst.getParent()))
      m_inst_to_shadow[br1] = a;
    if (!m_dm.dominates((BasicBlock *)br2, inst.getParent()))
      m_inst_to_shadow[br2] = a;
    m_taint_to_bb[a] = inst.getParent();
  }
}

bool TaintLogic::runOnFunction(Function &F) {
  if (F.isDeclaration())
    return false;
#if DEBUG_TAINT
  F.dump();
#endif
  LLVMContext &ctx = F.getContext();
  IRBuilder<> B(ctx);

  if (!m_errorFn) {
    assert(false);
  }

  std::vector<Instruction *> WorkList;
  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;
    // TODO: For now covering all types basically
    // Need to see what needs to be covered and what not
    WorkList.push_back(I);
  }

  BasicBlock *prevBB = WorkList.front()->getParent();
  BasicBlock *currBB = prevBB;

  m_topBB = currBB;
  B.SetInsertPoint(&*m_topBB->getFirstInsertionPt());

  addAllShadowTaintVars(B, WorkList);

  for (Instruction *I : WorkList) {
    currBB = I->getParent();
    if (currBB != prevBB) {
      prevBB = currBB;
    }
    if (isa<CallInst>(I)) {
      unsigned operands = I->getNumOperands();
      StringRef funcName = I->getOperand(operands - 1)->getName();
      if (funcName.compare("ifc_check_taint") == 0) {
        Value *var = I->getOperand(0);
        if (isa<GetElementPtrInst>(var)) {
          // TODO
          assert(false && "Not supported yet!");
        } else if (m_inst_to_shadow.find(var) != m_inst_to_shadow.end()) {
          Value *taintVar = m_inst_to_shadow[var];
          insertTaintCheck(F, B, *I, taintVar);
        }
      }
      continue;
    }

#if DEBUG_TAINT
    outs() << "Processing: ";
    I->print(outs());
    outs() << "\n";
    outs().flush();
#endif
    insertTaintLogic(B, *I);
  }

  return true;
}

bool TaintLogic::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  if (m_dumpOnly) {
    M.dump();
    return false;
  }

  LLVMContext &ctx = M.getContext();

  m_BoolTy = Type::getInt1Ty(ctx);

  if (HasErrorFunc) {
    AttrBuilder B;
    B.addAttribute(Attribute::NoReturn);
    B.addAttribute(Attribute::ReadNone);

    AttributeSet as = AttributeSet::get(ctx, AttributeSet::FunctionIndex, B);

    m_errorFn = dyn_cast<Function>(M.getOrInsertFunction(
        "verifier.error", as, Type::getVoidTy(ctx), nullptr));
  }

  bool change = false;
  for (Function &F : M) {
    change |= runOnFunction(F);
  }

  errs() << "-- Inserted " << m_TaintChecksAdded << " taint checks.\n";
  M.dump();
  return change;
}

void TaintLogic::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}
} // namespace seahorn

namespace seahorn {
llvm::Pass *createTaintLogicPass() { return new TaintLogic(); }
} // namespace seahorn

static llvm::RegisterPass<seahorn::TaintLogic> X("taint-logic",
                                                 "Insert taint tracking logic");
