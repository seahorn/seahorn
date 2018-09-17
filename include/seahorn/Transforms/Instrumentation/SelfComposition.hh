#ifndef __SELF_COMPOSITION__HH__
#define __SELF_COMPOSITION__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/DenseSet.h"

namespace seahorn
{
  using namespace llvm;

  class SelfComposition : public llvm::ModulePass
  {
    DominatorTreeBase<BasicBlock> m_postDm;
    DominatorTree m_dm;
    bool m_dumpOnly;
    Function * m_errorFn;
    CallGraph * m_CG; // Call graph of the program
    DataLayout * m_DL;

    BasicBlock* m_splitBB;
    std::vector<BasicBlock*> m_shadowBBs;
    DenseMap<const Value*, Value*> m_inst_to_shadow;
    DenseMap<Value*, Value*> m_inst_to_notaint;

    DenseMap<Value*, bool> m_varAssigned;

    DenseSet<Value*> m_high;
    DenseSet<Instruction*> m_traverse;

    DenseSet<BranchInst*> m_updatedBranches;
    DenseMap<Value*, Value*> m_replacedInst;


    Value* allocaForValue (IRBuilder<>& B, const AllocaInst *n, uint64_t size=0);

    Value* addShadowVar(IRBuilder<>& B, AllocaInst* op, uint64_t size=0);
    Value* getShadowVar(IRBuilder<>& B, const Value* var);

    BasicBlock* createErrorBlock (Function &F, IRBuilder<> B, AllocaInst* taintVar);
    void insertEqCheck(Function &F, IRBuilder<>& B, Instruction& inst, Value* taintVar);

    bool isSCRequired(Instruction* inst);
    GetElementPtrInst* cloneOrigGEP(GetElementPtrInst *gep, Instruction *shadow);

    void basicBlockPass(IRBuilder<> &B, BasicBlock *bb);
    void connectShadowBB(IRBuilder<> &B, BasicBlock *postDom);
    void updateInstruction(IRBuilder<> &B, Instruction* inst);
    bool isUncomposable(Instruction *inst, Instruction *store);

  public:

    static char ID;

    SelfComposition (bool dumpOnly = false) :
        m_postDm(true),
        m_dm(),
        m_dumpOnly(dumpOnly),
        llvm::ModulePass (ID), 
        m_errorFn (nullptr),
        m_CG (nullptr),
        m_splitBB(nullptr) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "SelfComposition";}
    
  };

}

#endif //__SELF_COMPOSITION__HH__
