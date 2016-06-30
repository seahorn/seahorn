

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"


#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstVisitor.h"


#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Support/SortTopo.hh"


#include "boost/range/algorithm/reverse.hpp"
using namespace llvm;
using namespace seahorn;

namespace
{
  class IntraBlockBuilder : InstVisitor<IntraBlockBuilder>
  {
    Function &m_func;
    dsa::Graph &m_graph;

    const DataLayout &m_dl;
    
    
    void visitAllocaInst (AllocaInst &AI);
    void visitPHINode (PHINode &PHI) {/* do nothing */}
    void visitSelectInst(SelectInst &SI);
    void visitLoadInst(LoadInst &LI);
    void visitStoreInst(StoreInst &SI);
    void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I);
    void visitAtomicRMWInst(AtomicRMWInst &I);
    void visitReturnInst(ReturnInst &RI);
    void visitVAArgInst(VAArgInst   &I);
    void visitIntToPtrInst(IntToPtrInst &I);
    void visitPtrToIntInst(PtrToIntInst &I);
    void visitBitCastInst(BitCastInst &I);
    void visitCmpInst(CmpInst &I) {/* do nothing */}
    void visitInsertValueInst(InsertValueInst& I) { /* ignore for now */ }
    void visitExtractValueInst(ExtractValueInst& I) { /* ignore for now */ }

    void visitGetElementPtrInst(User &GEP);
    void visitInstruction(Instruction &I);

    bool visitIntrinsic(CallSite CS, Function* F);
    void visitCallSite(CallSite CS);
    void visitVAStart(CallSite CS);

  public:
    IntraBlockBuilder (Function &func, dsa::Graph &graph,
                       const DataLayout &dl) : m_func(func), m_graph(graph), m_dl(dl) {}
    
    
  };
}
namespace seahorn
{
  namespace dsa
  {
    class Local : public ModulePass
    {
      const DataLayout *m_dl;
      TargetLibraryInfo *m_tli;
      
    public:
      static char ID;
      Local () : ModulePass (ID), m_dl (nullptr), m_tli (nullptr)
      {}
      
      void getAnalysisUsage (AnalysisUsage &AU) const override
      {
        AU.addRequired<DataLayoutPass> ();
        AU.addRequired<TargetLibraryInfo> ();
        AU.setPreservesAll ();
      }

      bool runOnModule (Module &M)
      {
        for (Function &F : M) runOnFunction (F);      
        return false;
      }

      bool runOnFunction (Function &F)
      {
        if (F.isDeclaration () || F.empty ()) return false;
        
        std::vector<const BasicBlock *> bbs;
        RevTopoSort (F, bbs);
        boost::reverse (bbs);
        
        for (const BasicBlock *bb : bbs) doIntraBlock (*bb);
        for (const BasicBlock *bb : bbs) doInterBlock (*bb);
        return false;
      }

      /// Compute DSA nodes for all instructions in the basic block
      void doIntraBlock (const BasicBlock &bb)
      {
        // run intra-block-visitor
        for (const Instruction &inst : bb)
          errs () << "visiting: " << inst << "\n";
      }

      /// Update DSA nodes for all the PHI-nodes based on the results
      /// of intra-block analysis
      void doInterBlock (const BasicBlock &bb)
      {
        // run inter-block-visitor
      }
      
    };

    char Local::ID = 0;

      
  }
}
