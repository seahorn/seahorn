

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

#include "llvm/Analysis/MemoryBuiltins.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Support/SortTopo.hh"


#include "boost/range/algorithm/reverse.hpp"
using namespace llvm;
using namespace seahorn;


namespace
{
  template<typename T>
  T gcd(T a, T b)
  {
    T c;
    while(b)
    {
      c = a % b;
      a = b;
      b = c;
    }
    return a;
  }
  
  class IntraBlockBuilder : InstVisitor<IntraBlockBuilder>
  {
    Function &m_func;
    dsa::Graph &m_graph;

    const DataLayout &m_dl;
    const TargetLibraryInfo &m_tli;
    
    bool isSkip (Instruction &I)
    {
      if (!I.getType ()->isPointerTy ()) return true;
      // XXX skip if only uses are external functions
      return false;
    }
    
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

    void visitGetElementPtrInst(GetElementPtrInst &I);
    void visitInstruction(Instruction &I);

    bool visitIntrinsic(CallSite CS, Function* F);
    void visitCallSite(CallSite CS);
    void visitVAStart(CallSite CS);

  public:
    IntraBlockBuilder (Function &func, dsa::Graph &graph,
                       const DataLayout &dl, const TargetLibraryInfo &tli) :
      m_func(func), m_graph(graph), m_dl(dl), m_tli (tli) {}
    
    
  };

  
  void IntraBlockBuilder::visitAllocaInst (AllocaInst &AI)
  {
    using namespace seahorn::dsa;
    assert (!m_graph.hasCell (AI));
    Node &n = m_graph.mkNode ();
    // TODO: record allocation site
    // TODO: mark as stack allocated
    Cell &res = m_graph.mkCell (AI);
    res.pointTo (n, 0);
  }
  void IntraBlockBuilder::visitSelectInst(SelectInst &SI)
  {
    using namespace seahorn::dsa;
    if (isSkip (SI)) return;
    
    Cell &res = m_graph.mkCell (SI);

    Cell thenC = m_graph.valueCell (*SI.getOperand (1));
    Cell elseC = m_graph.valueCell (*SI.getOperand (2));
    thenC.unify (elseC);
    res.pointTo (thenC, 0);
  }
  
  void IntraBlockBuilder::visitLoadInst(LoadInst &LI)
  {
    using namespace seahorn::dsa;
    if (isa<PointerType> (LI.getType ())) m_graph.mkCell (LI);
    
    Cell base = m_graph.valueCell (*LI.getPointerOperand ());
    if (base.isNull ()) return;

    base.addType (0, LI.getType ());
    // TODO: mark base as read
    
    // update/create the link
    if (isa<PointerType> (LI.getType ())) 
    {
      Cell &ptr = m_graph.mkCell (LI);
      if (!base.hasLink ())
      {
        Node &n = m_graph.mkNode ();
        ptr.setLink (0, Cell (&n, 0));
      }
      ptr.pointTo (base.getLink ());
    }
  }
  
  void IntraBlockBuilder::visitStoreInst(StoreInst &SI)
  {
    using namespace seahorn::dsa;
    Cell base = m_graph.valueCell (*SI.getPointerOperand ());
    if (base.isNull ()) return;

    // TODO: mark base as modified

    // XXX: potentially it is enough to update size only at this point
    base.addType (0, SI.getValueOperand ()->getType ());
    
    if (isa<PointerType> (SI.getValueOperand ()->getType ()))
    {
      Cell val = m_graph.valueCell (*SI.getValueOperand ());
      base.addLink (0, val);
    }
  }

  
  void IntraBlockBuilder::visitBitCastInst(BitCastInst &I)
  {
    if (isSkip (I)) return;
    dsa::Cell &res = m_graph.mkCell (I);
    dsa::Cell arg = m_graph.valueCell (*I.getOperand (0));
    if (arg.isNull ()) return;
    res.pointTo (arg);
  }
  
  /**
     Computes an offset of a gep instruction for a given type and a
     sequence of indicies.

     The first element of the pair is the fixed offset. The second is
     a gcd of the variable offset.
   */
  std::pair<uint64_t, uint64_t> computeGetOffset (Type *ptrTy, ArrayRef<Value *> Indicies,
                                                  const DataLayout &dl)
{
    unsigned ptrSz = dl.getPointerSizeInBits ();
    Type *Ty = ptrTy;
    assert (Ty->isPointerTy ());
    
    // numeric offset
    uint64_t noffset = 0;

    // divisor
    uint64_t divisor = 0;
    
    generic_gep_type_iterator<Value* const*>
      TI = gep_type_begin (ptrTy, Indicies);
    for (unsigned CurIDX = 0, EndIDX = Indicies.size (); CurIDX != EndIDX;
         ++CurIDX, ++TI)
    {
      if (StructType *STy = dyn_cast<StructType> (*TI))
      {
        unsigned fieldNo = cast<ConstantInt> (Indicies [CurIDX])->getZExtValue ();
        noffset += dl.getStructLayout (STy)->getElementOffset (fieldNo);
        Ty = STy->getElementType (fieldNo);
      }
      else
      {
        Ty = cast<SequentialType> (Ty)->getElementType ();
        uint64_t sz = dl.getTypeStoreSize (Ty);
        if (ConstantInt *ci = dyn_cast<ConstantInt> (Indicies [CurIDX]))
        {
          int64_t arrayIdx = ci->getSExtValue ();
          noffset += (uint64_t)arrayIdx * sz;
        }
        else
          divisor = divisor == 0 ? sz : gcd (divisor, sz);
      }
    }
    
    return std::make_pair (noffset, divisor);
  }    
  
  
  void IntraBlockBuilder::visitGetElementPtrInst(GetElementPtrInst &I)
  {
    Value *ptr = I.getPointerOperand ();
    assert (m_graph.hasCell (*ptr));
    dsa::Cell &base = m_graph.mkCell (*ptr);
    assert (!base.isNull ());

    assert (!m_graph.hasCell (I));
    dsa::Cell &res = m_graph.mkCell (I);
    
    dsa::Node *baseNode = base.getNode ();
    if (baseNode->isCollapsed ())
    {
      res.pointTo (*baseNode, 0);
      return;
    }
    
    SmallVector<Value*, 8> indexes (I.op_begin () + 1, I.op_end ());
    auto off = computeGetOffset (ptr->getType (), indexes, m_dl);
    if (off.second)
    {
      // create a node representing the array
      dsa::Node &n = m_graph.mkNode ();
      n.setArraySize (off.second);
      // result of the gep points into that array at the gep offset
      // plus the offset of the base
      res.pointTo (n, off.first + base.getOffset ());
      // finally, unify array with the node of the base 
      n.unify (*baseNode);
    }
    else
      res.pointTo (base, off.first);
  }
  
  
  void IntraBlockBuilder::visitCallSite(CallSite CS)
  {
    using namespace dsa;
    if (isSkip (*CS.getInstruction ())) return;
    
    if (llvm::isAllocationFn (CS.getInstruction (), &m_tli, true))
    {
      assert (CS.getInstruction ());
      Node &n = m_graph.mkNode ();
      // TODO: record allocation site
      // TODO: mark as heap allocated
      Cell &res = m_graph.mkCell (*CS.getInstruction ());
      res.pointTo (n, 0);
      return;  
    }

    // TODO: handle other cases
  }
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
