#ifndef __TAINT_LOGIC__HH__
#define __TAINT_LOGIC__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

namespace seahorn
{
  using namespace llvm;
  
  class TaintLogic : public llvm::ModulePass
  {

    bool m_dumpOnly;
    Function * m_errorFn;
    unsigned m_TaintChecksAdded;
    CallGraph * m_CG; // Call graph of the program

    BasicBlock* m_topBB;
    std::vector<Value*> m_shadows;
    DenseMap<const Value*, Value*> m_inst_to_shadow;
    DenseMap<const Value*, BasicBlock*> m_taint_to_bb;
    DominatorTreeBase<BasicBlock, true> m_dm;
    Type *m_BoolTy;

    Value* allocaForValue (IRBuilder<>& B, const Value *n, uint64_t size=0);
    unsigned getId (const Instruction *n);

    bool isTaintVarExists(const Value* val);
    Value* addShadowTaintVar(IRBuilder<>& B, Value* op, uint64_t size=0);
    Value* getShadowTaintVar(IRBuilder<>& B, Value* val);
    bool isTaintLogicRequired(Instruction& inst);
    void insertTaintLogic(IRBuilder<>& B, Instruction& inst);

    BasicBlock* createErrorBlock (Function &F, IRBuilder<> B, AllocaInst* taintVar);
    void insertTaintCheck(Function &F, IRBuilder<>& B, Instruction& inst, Value* taintVar);

    Value* getOrCreateShadowForInst(IRBuilder<>& B, Instruction& inst);
    void addAllShadowTaintVars(IRBuilder<> &B, std::vector<Instruction*>& WorkList);

    Value* getShadowTaintForGEP(IRBuilder<> B, Value* val)
    {
        assert(isa<GetElementPtrInst>(val));
        GetElementPtrInst& gep = *dyn_cast<GetElementPtrInst>(val);
        Value *ptr = gep.getPointerOperand();
        Value *taintVar = nullptr;
        if (isa<GetElementPtrInst>(ptr)){
            ptr = getShadowTaintForGEP(B, ptr);
            if (ptr != NULL) {
                unsigned ptrIdx = gep.getPointerOperandIndex();
                unsigned numInd = gep.getNumIndices();
                // TODO: Need to understand if more than 2 indices
                // TODO: are possible, and what is the exact semantics
                assert (numInd <= 2 && "not supported");
                std::vector<Value*> indices(gep.idx_begin(), gep.idx_end());
                if (gep.isInBounds())
                    taintVar = B.CreateInBoundsGEP(ptr, indices);
                else
                    taintVar = B.CreateGEP(ptr, indices);
            }
        }
        else {
            auto it = m_inst_to_shadow.find(ptr);
            if (it != m_inst_to_shadow.end()) {
                taintVar = it->second;
                unsigned ptrIdx = gep.getPointerOperandIndex();
                unsigned numInd = gep.getNumIndices();
                // TODO: Need to understand if more than 2 indices
                // TODO: are possible, and what is the exact semantics
                assert (numInd <= 2 && "not supported");
                std::vector<Value*> indices(gep.idx_begin(), gep.idx_end());
                if (gep.isInBounds())
                    taintVar = B.CreateInBoundsGEP(taintVar, indices);
                else
                    taintVar = B.CreateGEP(taintVar, indices);
            }
        }

        return taintVar;
    }

    Value* createShadowTaintForGEP(IRBuilder<> B, Value* val)
    {
        assert(isa<GetElementPtrInst>(val));
        GetElementPtrInst& gep = *dyn_cast<GetElementPtrInst>(val);
        Value *ptr = gep.getPointerOperand();
        if (isa<GetElementPtrInst>(ptr)){
            return createShadowTaintForGEP(B, ptr);
        }
        Value *shadow = NULL;
        auto it = m_inst_to_shadow.find(ptr);
        if (it == m_inst_to_shadow.end()) {
            Type *t = ((PointerType*)gep.getPointerOperandType())->getElementType();
            unsigned eSize = 0;
            if (t->isArrayTy()) {
                eSize = ((ArrayType*)t)->getNumElements();
            }
            else if (t->isStructTy()) {
                eSize = ((StructType*)t)->getNumElements();
            }
            shadow = addShadowTaintVar(B, ptr, eSize);
        }
        else
            shadow = it->second;

        return shadow;
    }

    unsigned getNumTaintElements(Value *op)
    {
        unsigned eSize = 1;
        Type *t = op->getType();
        if (t->isPointerTy()) {
            Type *et = ((PointerType*)t)->getElementType();
            if (et->isArrayTy()) {
                eSize = ((ArrayType*)et)->getNumElements();
            }
            else if (et->isStructTy()) {
                eSize = ((StructType*)et)->getNumElements();
            }
        }
        return eSize;
    }

    Value* createLoadTaint(IRBuilder<> &B, Value *taint, unsigned element)
    {
        Value *load = nullptr;
        Type *t = taint->getType();
        if (t->isPointerTy() &&
            (((PointerType*)t)->getElementType()->isArrayTy() ||
            ((PointerType*)t)->getElementType()->isStructTy()))
        {
            Type *et = ((PointerType*)t)->getElementType();
            unsigned size = 0;
            if (et->isArrayTy()) {
                size = ((ArrayType*)et)->getNumElements();
            }
            else if (et->isStructTy()) {
                size = ((StructType*)et)->getNumElements();
            }

            Value *v = B.CreateConstGEP2_32(ArrayType::get(m_BoolTy, size), taint, 0, element);
            load = (Value*)B.CreateAlignedLoad(v, 1);
        }
        else
            load = (Value*)B.CreateAlignedLoad(taint, 1);

        return load;
    }


  public:

    static char ID;

    TaintLogic (bool dumpOnly = false) :
        m_dm(),
        m_dumpOnly(dumpOnly),
        llvm::ModulePass (ID), 
        m_errorFn (nullptr),
        m_TaintChecksAdded (0),
        m_CG (nullptr) { }
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual StringRef getPassName () const {return "TaintLogic";}
    
  };

}

#endif
