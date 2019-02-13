/*
 * Do self composition

 * Limitation: XXX.
 */

#include "seahorn/Transforms/Instrumentation/SelfComposition.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <list>
#include <unordered_set>

#define DEBUG_SC 1

static llvm::cl::opt<bool> HasErrorFunc(
    "self-composition-has-error-function",
    llvm::cl::desc("Available verifier.error function to denote error."),
    llvm::cl::init(true));

namespace seahorn {
using namespace llvm;

char SelfComposition::ID = 0;

BasicBlock *SelfComposition::createErrorBlock(Function &F, IRBuilder<> B,
                                              AllocaInst *taintVar) {
  BasicBlock *errBB = BasicBlock::Create(
      B.getContext(), "EqCheck_" + taintVar->getName().str(), &F);

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

void SelfComposition::insertEqCheck(Function &F, IRBuilder<> &B,
                                    Instruction &inst, Value *var) {
  // Create error blocks
  LLVMContext &ctx = B.getContext();
  BasicBlock *err_sc_bb = BasicBlock::Create(ctx, "sc_error_bb", &F);

  B.SetInsertPoint(err_sc_bb);
  CallInst *ci_eq = B.CreateCall(m_errorFn);
  ci_eq->setDebugLoc(inst.getDebugLoc());
  B.CreateUnreachable();

  B.SetInsertPoint(&inst);

  BasicBlock *OldBB0 = inst.getParent();
  BasicBlock *Cont0 = OldBB0->splitBasicBlock(B.GetInsertPoint());
  OldBB0->getTerminator()->eraseFromParent();
  BranchInst::Create(Cont0, OldBB0);

  B.SetInsertPoint(Cont0->getFirstNonPHI());

  /// --- IFC: add check var == shadow
  Value *shadow = m_inst_to_shadow[var];
  Value *eqCheck =
      B.CreateICmpEQ(B.CreateLoad(var), B.CreateLoad(shadow), "eq_check");

  BasicBlock *OldBB1 = Cont0;
  BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint());
  OldBB1->getTerminator()->eraseFromParent();
  BranchInst::Create(Cont1, err_sc_bb, eqCheck, OldBB1);
}

Value *SelfComposition::allocaForValue(IRBuilder<> &B, const AllocaInst *v,
                                       uint64_t size) {
  auto it = m_inst_to_shadow.find(v);
  if (it != m_inst_to_shadow.end())
    return it->second;

  std::string name = v->getName().str() + "_shadow";
  Type *varType = v->getAllocatedType();
  AllocaInst *a = B.CreateAlloca(varType, 0, name);
  a->setAlignment(v->getAlignment());
  m_inst_to_shadow[v] = a;
  return a;
}

Value *SelfComposition::getShadowVar(IRBuilder<> &B, const Value *val) {
  Value *shadowVar = nullptr;

  if (m_inst_to_shadow.find(val) != m_inst_to_shadow.end())
    shadowVar = m_inst_to_shadow[val];

  return shadowVar;
}

Value *SelfComposition::addShadowVar(IRBuilder<> &B, AllocaInst *var,
                                     uint64_t size) {
  auto it = m_inst_to_shadow.find(var);
  if (it != m_inst_to_shadow.end())
    return it->second;

  B.SetInsertPoint(var);
  Value *a = allocaForValue(B, var, size);
  return a;
}

GetElementPtrInst *SelfComposition::cloneOrigGEP(GetElementPtrInst *gep,
                                                 Instruction *shadow) {
  GetElementPtrInst *clone = dyn_cast<GetElementPtrInst>(gep->clone());
  unsigned idx_i = 0;
  for (auto itIdx = clone->op_begin(), end = clone->op_end(); itIdx != end;
       itIdx++, idx_i++) {
    Value *op = *itIdx;
    if (clone->getPointerOperand() == op) {
      if (isa<GetElementPtrInst>(op))
        *itIdx = cloneOrigGEP((GetElementPtrInst *)op,
                              (Instruction *)m_inst_to_shadow[op]);
      continue;
    }

    *itIdx = shadow->getOperand(idx_i);
  }
  clone->insertBefore(shadow);
  return clone;
}

bool SelfComposition::isSCRequired(Instruction *inst) {
  if (m_traverse.find(inst) != m_traverse.end())
    return false;
  m_traverse.insert(inst);
  bool scRequired = false;
  if (isa<AllocaInst>(inst)) {
    scRequired = m_high.find(inst) != m_high.end();
  }
  for (auto it = inst->op_begin(), end = inst->op_end();
       it != end && !scRequired; it++) {
    Value *op = *it;
    auto highIt = m_high.find(op);
    // auto taintIt = m_inst_to_taint.find(op);
    bool noTaint =
        false; //(taintIt != m_inst_to_taint.end()) && !taintIt->second;
    if (highIt != m_high.end() && !noTaint)
      scRequired = true;
    else if (isa<Instruction>(op))
      scRequired = isSCRequired((Instruction *)op);
  }

  m_traverse.erase(inst);
  return scRequired;
}

bool SelfComposition::isUncomposable(Instruction *inst, Instruction *store) {
  auto noTaint = m_inst_to_notaint.find(inst);
  m_dm.recalculate(*(inst->getParent()->getParent()));
  if (noTaint != m_inst_to_notaint.end() &&
      m_dm.dominates((Instruction *)noTaint->second, store))
    return true;

  Value *shadow = m_inst_to_shadow[inst];
  Value *shadowStore = m_inst_to_shadow[store];
  auto repIt = m_replacedInst.find(shadow);
  if (repIt != m_replacedInst.end() &&
      m_dm.dominates((Instruction *)repIt->second, (Instruction *)shadowStore))
    return true;

  return false;
}

void SelfComposition::basicBlockPass(IRBuilder<> &B, BasicBlock *bb) {
  outs() << "Analyzing " << bb->getName() << "\n";
  m_postDm.recalculate(*(bb->getParent()));
  if (m_splitBB != nullptr && m_postDm.dominates(bb, m_splitBB) &&
      bb->getTerminator()->getNumSuccessors() <= 1 &&
      (bb->getTerminator()->getNumSuccessors() == 0 ||
       !isa<PHINode>(
           bb->getTerminator()->getSuccessor(0)->getInstList().front()))) {
    ValueToValueMapTy instMap;
    BasicBlock *shadowBB =
        CloneBasicBlock(bb, instMap, "_shadow", bb->getParent());
    m_inst_to_shadow[bb] = shadowBB;
    m_shadowBBs.push_back(shadowBB);
    connectShadowBB(B, bb);
    return;
  }
  TerminatorInst *terminator = bb->getTerminator();
  bool succHasPhi = false;
  for (unsigned s = 0; s < terminator->getNumSuccessors() && !succHasPhi; s++) {
    BasicBlock *ss = terminator->getSuccessor(s);
    if (isa<PHINode>(*(ss->begin())))
      succHasPhi = true;
  }
  // For now we only support branch instructions and return
  assert(isa<BranchInst>(terminator) || isa<ReturnInst>(terminator));
  if (m_splitBB != nullptr ||
      ((isSCRequired(terminator) || succHasPhi) &&
       terminator->getNumSuccessors() > 1) ||
      isa<PHINode>(*(bb->begin()))) {

    if (m_splitBB == nullptr)
      m_splitBB = bb;

    ValueToValueMapTy instMap;
    BasicBlock *shadowBB =
        CloneBasicBlock(bb, instMap, "_shadow", bb->getParent());
    m_inst_to_shadow[bb] = shadowBB;
    m_shadowBBs.push_back(shadowBB);
  }
}

void SelfComposition::connectShadowBB(IRBuilder<> &B, BasicBlock *postDom) {
  // Now update the shadow BBs
  std::list<BasicBlock *> WorkList;
  DenseSet<BasicBlock *> done;
  done.insert(postDom);
  WorkList.push_back(m_splitBB);
  while (WorkList.size() > 0) {
    BasicBlock *bb = WorkList.front();
    WorkList.pop_front();
    if (done.find(bb) != done.end())
      continue;
    done.insert(bb);
    BasicBlock *shadowBB = (BasicBlock *)m_inst_to_shadow[bb];
    if (shadowBB == nullptr)
      continue;
    BranchInst *branch = dyn_cast<BranchInst>(shadowBB->getTerminator());
    for (unsigned i = 0; i < branch->getNumSuccessors(); i++) {
      BasicBlock *succ = branch->getSuccessor(i);
      WorkList.push_back(succ);
      branch->setSuccessor(i, (BasicBlock *)m_inst_to_shadow[succ]);
    }
  }

  // Switch the post-dom's successor to the shadow split
  BasicBlock *shadowSplit = (BasicBlock *)m_inst_to_shadow[m_splitBB];
  BasicBlock *postDomShadow = (BasicBlock *)m_inst_to_shadow[postDom];

  if (isa<BranchInst>(postDom->getTerminator())) {
    BranchInst *branch = dyn_cast<BranchInst>(postDom->getTerminator());
    BranchInst *branchShadow =
        dyn_cast<BranchInst>(postDomShadow->getTerminator());

    if (branch->isUnconditional()) {
      BasicBlock *origSucc = dyn_cast<BasicBlock>(branch->getOperand(0));
      branch->setSuccessor(0, shadowSplit);
      branchShadow->setSuccessor(0, origSucc);
      m_updatedBranches.insert(branchShadow);
    } else {
      assert(false);
    }
  } else {
    ReturnInst *ret = dyn_cast<ReturnInst>(postDom->getTerminator());
    B.SetInsertPoint(ret);
    B.CreateBr(shadowSplit);
    ret->eraseFromParent();
  }

  m_splitBB = nullptr;
}

void SelfComposition::updateInstruction(IRBuilder<> &B, Instruction *inst) {
  // If this is a store instruction, add the destination as a shadow
  if (isa<StoreInst>(inst)) {
    Value *dst = inst->getOperand(1);
    auto shadowDst = m_inst_to_shadow.find(dst);
    if (shadowDst == m_inst_to_shadow.end()) {
      uint64_t size = 0;
      if (isa<GetElementPtrInst>(dst)) {
        Type *t = ((PointerType *)dyn_cast<GetElementPtrInst>(dst)
                       ->getPointerOperandType())
                      ->getElementType();
        size = ((ArrayType *)t)->getNumElements();
        dst = dyn_cast<GetElementPtrInst>(dst)->getPointerOperand();
      }
      addShadowVar(B, dyn_cast<AllocaInst>(dst), size);
    }
  }

  assert(m_inst_to_shadow.find(inst) != m_inst_to_shadow.end());
  Instruction *shadow = dyn_cast<Instruction>(m_inst_to_shadow[inst]);
  if (PHINode *phi = dyn_cast<PHINode>(shadow)) {
    SmallVector<BasicBlock*,8> preds;
    for (auto it = pred_begin(phi->getParent()),
              end = pred_end(phi->getParent());
         it != end; it++) {
      BasicBlock *p = *it;
      if (!p->getName().endswith_lower("_shadow"))
        preds.push_back(p);
    }
    LOG("ifc_sc",
        if (preds.size() > 1) {
            errs() << "preds size: " << preds.size() << "\n";
            for (auto *bb : preds) {
                errs() << *bb << "\n\n";
            }
        }
        );
    assert(preds.size() <= 1);
    unsigned opIdx = 0;
    auto itVal = phi->op_begin();
    for (auto itB = phi->block_begin(), endB = phi->block_end(); itB != endB;
         itB++, opIdx++, itVal++) {
      Value *inB = *itB;
      Value *inV = *itVal;
      Value *shadowB = getShadowVar(B, inB);
      Value *shadowV = getShadowVar(B, inV);
      if (shadowB != nullptr) {
        *itB = (BasicBlock *)shadowB;
        assert(isa<Constant>(inV) || shadowV != nullptr);
      }

      if (shadowV != nullptr) {
        *itVal = shadowV;
      }

      if (isa<Instruction>(inV) && isSCRequired((Instruction *)inV))
        m_high.insert(inV);
    }

    for (auto itB = phi->block_begin(), endB = phi->block_end(); itB != endB;
         itB++) {
      BasicBlock *inB = *itB;
      if (!inB->getName().endswith_lower("_shadow"))
        *itB = preds[0];
    }

  } else {
    for (auto it = shadow->op_begin(), end = shadow->op_end(); it != end;
         it++) {
      Value *op = *it;
      Value *shadowOp = getShadowVar(B, op);
      if (shadowOp != nullptr) {
        // auto repIt = m_replacedInst.find(shadowOp);
        // if (repIt != m_replacedInst.end())
        //    *it = repIt->second;
        // else
        *it = shadowOp;
      }
    }
  }

  Instruction *insertPoint = inst;
  if (isa<StoreInst>(inst)) {
    Value *dst = inst->getOperand(1);
    Value *shadowDst = m_inst_to_shadow[dst];
    Value *src = inst->getOperand(0);
    Value *shadowSrc = m_inst_to_shadow[src];
    if (isa<LoadInst>(src))
      src = ((Instruction *)src)->getOperand(0);
    assert(dst != nullptr);
    if (isa<Instruction>(src)) {
      m_dm.recalculate(*(inst->getParent()->getParent()));
      if ((isUncomposable((Instruction *)src, inst) ||
           isUncomposable((Instruction *)dst, inst))) //||
      //! isSCRequired(inst)) // XXX: This one is an optimization - if problem
      //! occurs, look here
      {
        Value *origDst = dst;
        Type *t = dst->getType();
        if (isa<GetElementPtrInst>(dst)) {
          GetElementPtrInst *gep =
              cloneOrigGEP((GetElementPtrInst *)dst, (Instruction *)shadowDst);
          origDst = gep;
          t = ((GetElementPtrInst *)dst)->getResultElementType();
        }
        B.SetInsertPoint(shadow);
        int align = m_DL->getTypeAllocSize(t);
        Value *loadOrig = B.CreateAlignedLoad(origDst, align);
        StringRef name = src->getName();
        m_replacedInst[shadowSrc] = loadOrig;
        loadOrig->setName(name);
        //((Instruction*)shadowSrc)->eraseFromParent();
        auto srcIt = shadow->op_begin();
        *srcIt = loadOrig;
        insertPoint = (Instruction *)loadOrig;
      }
    }
    m_varAssigned[dst] = true; // XXX: Unused currently
    if (isa<Instruction>(src) && isSCRequired((Instruction *)src)) {
      if (isa<GetElementPtrInst>(dst))
        m_high.insert(((GetElementPtrInst *)dst)->getPointerOperand());
      else
        m_high.insert(dst);
    }
  }
}

bool SelfComposition::runOnFunction(Function &F) {
  if (F.isDeclaration())
    return false;
#if DEBUG_SC
  F.print(outs());
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

  std::vector<Instruction *> checkInst;
  for (Instruction *I : WorkList) {
    if (isa<CallInst>(I)) {
      unsigned operands = I->getNumOperands();
      StringRef funcName = I->getOperand(operands - 1)->getName();
      if (funcName.compare("ifc_set_secret") == 0) {
        Value *var = I->getOperand(0);
        var = var->stripPointerCasts();
        assert(isa<AllocaInst>(var)); // TODO: just for now
        m_high.insert(var);
        Value *shadow = addShadowVar(B, (AllocaInst *)var, 0);
        I->eraseFromParent();
      } else if (funcName.startswith_lower("ifc_set_notaint")) {
        Value *var = I->getOperand(0);
        var = var->stripPointerCasts();
        assert(isa<AllocaInst>(var)); // TODO: just for now
        m_inst_to_notaint[var] = I;   // I->getNextNode();
      } else if (funcName.compare("ifc_check_out") == 0) {
        checkInst.push_back(I);
      }
    } else if (isa<AllocaInst>(I)) {
      m_varAssigned[(AllocaInst *)I] = false;
    }
  }
  WorkList.clear();
  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;
    // TODO: For now covering all types basically
    // Need to see what needs to be covered and what not
    WorkList.push_back(I);
  }

  std::vector<BasicBlock *> BBWorkList;
  for (auto i = F.begin(), e = F.end(); i != e; ++i) {
    BasicBlock *bb = &*i;
    // TODO: For now covering all types basically
    // Need to see what needs to be covered and what not
    BBWorkList.push_back(bb);
  }

  for (BasicBlock *bb : BBWorkList) {
    // doSelfComposition(B, bb);
    basicBlockPass(B, bb);
  }

  for (BasicBlock *bb : BBWorkList) {
    auto it = m_inst_to_shadow.find(bb);
    if (it != m_inst_to_shadow.end()) {
      BasicBlock *shadowBB = dyn_cast<BasicBlock>(it->second);
      for (auto instIt = bb->begin(), end = bb->end(),
                shadowIt = shadowBB->begin();
           instIt != end; instIt++, shadowIt++) {
        Value *from = &*instIt, *to = &*shadowIt;
        m_inst_to_shadow[from] = to;
      }
    } else {
      std::vector<Instruction *> instructions;
      for (auto instIt = bb->begin(), end = bb->end(); instIt != end;
           instIt++) {
        Instruction *inst = &*instIt;
        instructions.push_back(inst);
      }
      for (Instruction *inst : instructions) {
        if (isa<TerminatorInst>(inst) ||
            inst->getName().endswith_lower("_shadow") ||
            m_inst_to_shadow.find(inst) != m_inst_to_shadow.end()) {
          continue;
        }
        Instruction *shadow = inst->clone();
        if (inst->getName().str() != "") {
          std::string name = inst->getName().str() + "_shadow";
          shadow->setName(name);
        }
        shadow->insertAfter(inst);
        m_inst_to_shadow[inst] = shadow;
      }
    }
  }

  for (BasicBlock *bb : BBWorkList) {
    for (auto instIt = bb->begin(), end = bb->end(); instIt != end; instIt++) {
      Instruction *inst = &*instIt;
      auto it = m_inst_to_shadow.find(inst);
      if (it != m_inst_to_shadow.end()) {
        if (isa<BranchInst>(inst) &&
            m_updatedBranches.find((BranchInst *)it->second) !=
                m_updatedBranches.end()) {
          continue;
        }
        updateInstruction(B, inst);
      } else {
        auto itBB = m_inst_to_shadow.find(bb);
        assert(itBB == m_inst_to_shadow.end());
      }
    }
  }

  for (Instruction *I : checkInst) {
    unsigned operands = I->getNumOperands();
    Value *var = I->getOperand(0);
    Instruction *shadowInst = (Instruction *)m_inst_to_shadow[I];
    if (shadowInst->getParent() != I->getParent())
      I = shadowInst;
    if (isa<GetElementPtrInst>(var)) {
      // TODO
      assert(false && "Not supported yet!");
    } else {
      insertEqCheck(F, B, *I, var);
    }
  }

  return true;
}

bool SelfComposition::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  if (m_dumpOnly) {
    M.print(errs(), nullptr);
    return false;
  }

  m_DL = new DataLayout(&M);
  LLVMContext &ctx = M.getContext();

  if (HasErrorFunc) {
    AttrBuilder B;
    B.addAttribute(Attribute::NoReturn);
    B.addAttribute(Attribute::ReadNone);

    AttributeList as = AttributeList::get(ctx, AttributeList::FunctionIndex, B);

    m_errorFn = dyn_cast<Function>(M.getOrInsertFunction(
        "verifier.error", as, Type::getVoidTy(ctx), nullptr));
  }

  bool change = false;
  for (Function &F : M) {
    change |= runOnFunction(F);
  }

  M.print(errs(), nullptr);
  return change;
}

void SelfComposition::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}
} // namespace seahorn

namespace seahorn {
llvm::Pass *createSelfCompositionPass() { return new SelfComposition(); }
} // namespace seahorn
static llvm::RegisterPass<seahorn::SelfComposition> X("self-composition",
                                                      "Do self composition");
