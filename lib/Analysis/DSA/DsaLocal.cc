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

#include "llvm/ADT/DenseSet.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/Local.hh"
#include "seahorn/Support/SortTopo.hh"

#include "boost/range/algorithm/reverse.hpp"
#include "boost/make_shared.hpp"

#include "avy/AvyDebug.h"

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
  
  class InterBlockBuilder : public InstVisitor<InterBlockBuilder>
  {
    friend class InstVisitor<InterBlockBuilder>;
    dsa::Graph &m_graph;
    
    void visitPHINode (PHINode &PHI);
  public:
    InterBlockBuilder (dsa::Graph &g) : m_graph (g) {}
  };
  
  void InterBlockBuilder::visitPHINode (PHINode &PHI)
  {

    if (!PHI.getType ()->isPointerTy ()) return;

    assert (m_graph.hasCell (PHI));
    dsa::Cell &phi = m_graph.mkCell (PHI);
    for (unsigned i = 0, e = PHI.getNumIncomingValues (); i < e; ++i)
    {
      Value &v = *PHI.getIncomingValue (i);
      assert (m_graph.hasCell (v));
      phi.unify (m_graph.mkCell (v));
    }
  }
  
  class IntraBlockBuilder : public InstVisitor<IntraBlockBuilder>
  {
    friend class InstVisitor<IntraBlockBuilder>;
    Function &m_func;
    dsa::Graph &m_graph;

    const DataLayout &m_dl;
    const TargetLibraryInfo &m_tli;
    
    bool isSkip (Value &V)
    {
      if (!V.getType ()->isPointerTy ()) return true;
      // XXX skip if only uses are external functions
      return false;
    }
    
    void visitAllocaInst (AllocaInst &AI);
    void visitSelectInst(SelectInst &SI);
    void visitLoadInst(LoadInst &LI);
    void visitStoreInst(StoreInst &SI);
    // void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I);
    // void visitAtomicRMWInst(AtomicRMWInst &I);
    void visitReturnInst(ReturnInst &RI);
    // void visitVAArgInst(VAArgInst   &I);
    void visitIntToPtrInst(IntToPtrInst &I);
    void visitPtrToIntInst(PtrToIntInst &I);
    void visitBitCastInst(BitCastInst &I);
    void visitCmpInst(CmpInst &I) {/* do nothing */}
    void visitInsertValueInst(InsertValueInst& I); 
    void visitExtractValueInst(ExtractValueInst& I); 

    void visitGetElementPtrInst(GetElementPtrInst &I);
    void visitInstruction(Instruction &I);

    void visitMemSetInst(MemSetInst &I);            
    void visitMemTransferInst(MemTransferInst &I)  ;
    
    void visitCallSite(CallSite CS);
    // void visitVAStart(CallSite CS);

  public:
    IntraBlockBuilder (Function &func, dsa::Graph &graph,
                       const DataLayout &dl, const TargetLibraryInfo &tli) :
      m_func(func), m_graph(graph), m_dl(dl), m_tli (tli) {}
    
    
  };

  
  
  void IntraBlockBuilder::visitInstruction(Instruction &I)
  {
    if (isSkip (I)) return;
    
    m_graph.mkCell (I).
      pointTo (m_graph.mkNode(), 0);
  }
  
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
    if (!isSkip (LI)) m_graph.mkCell (LI);
    
    Cell base = m_graph.valueCell (*LI.getPointerOperand ());
    if (base.isNull ()) return;

    base.addType (0, LI.getType ());
    // TODO: mark base as read
    
    // update/create the link
    if (!isSkip (LI)) 
    {
      if (!base.hasLink ())
      {
        Node &n = m_graph.mkNode ();
        base.setLink (0, Cell (&n, 0));
      }
      Cell &ptr = m_graph.mkCell (LI);
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
    base.growSize (0, SI.getValueOperand ()->getType ());
    base.addType (0, SI.getValueOperand ()->getType ());
    
    if (isa<PointerType> (SI.getValueOperand ()->getType ()))
    {
      Cell val = m_graph.valueCell (*SI.getValueOperand ());
      assert (!val.isNull ());
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
  std::pair<uint64_t, uint64_t> computeGepOffset (Type *ptrTy, ArrayRef<Value *> Indicies,
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
  
  /// Computes offset into an indexed type
  uint64_t computeIndexedOffset (Type *ty, ArrayRef<unsigned> indecies,
                                 const DataLayout &dl)
  {
    uint64_t offset = 0;
    for (unsigned idx : indecies)
    {
      if (StructType *sty = dyn_cast<StructType> (ty))
      {
        const StructLayout *layout = dl.getStructLayout (sty);
        offset += layout->getElementOffset (idx);
        ty = sty->getElementType (idx);
      }
      else
      {
        ty = cast<SequentialType> (ty)->getElementType ();
        offset += idx * dl.getTypeAllocSize (ty);
      }
    }
    return offset;
  }
  
  void IntraBlockBuilder::visitGetElementPtrInst(GetElementPtrInst &I)
  {
    Value *ptr = I.getPointerOperand ();
    assert (m_graph.hasCell (*ptr) || isa<GlobalValue> (ptr));
    dsa::Cell base = m_graph.valueCell (*ptr);
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
    auto off = computeGepOffset (ptr->getType (), indexes, m_dl);
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
  
  void IntraBlockBuilder::visitInsertValueInst(InsertValueInst& I)
  {
    // TODO: set read/mod/alloc flags
    assert (I.getAggregateOperand ()->getType () == I.getType ());
    using namespace dsa;
    Cell &c = m_graph.mkCell (I);

    // make sure that the aggregate has a cell
    Cell op = m_graph.valueCell (*I.getAggregateOperand ());
    if (op.isNull ())
    {
      // -- create a node for the aggregate
      Cell &t = m_graph.mkCell (*I.getAggregateOperand ());
      t.pointTo (m_graph.mkNode (), 0);
      op = t;
    }
    
    c.unify (op);

    // -- update type record
    Value &v = *I.getInsertedValueOperand ();
    uint64_t offset = computeIndexedOffset (I.getAggregateOperand ()->getType (),
                                            I.getIndices (), m_dl);
    Cell out (op, offset);
    out.growSize (0, v.getType ());
    out.addType (0, v.getType ());
    
    // -- update link 
    if (!isSkip (v))
    {
      Cell vCell = m_graph.valueCell (v);
      assert (!vCell.isNull ());
      out.addLink (0, vCell);
    }
  }
  
  void IntraBlockBuilder::visitExtractValueInst(ExtractValueInst& I)
  {
    // TODO: set read/mod/alloc flags
    using namespace dsa;
    Cell op = m_graph.valueCell (*I.getAggregateOperand ());
    if (op.isNull ())
    {
      Cell &t = m_graph.mkCell (*I.getAggregateOperand ());
      t.pointTo (m_graph.mkNode (), 0);
      op = t;
    }
    
    uint64_t offset = computeIndexedOffset (I.getAggregateOperand ()->getType (),
                                            I.getIndices (), m_dl);
    Cell in (op, offset);

    // -- update type record
    in.addType (0, I.getType ());
    
    if (!isSkip (I))
    {
      // -- create a new node if there is no link at this offset yet
      if (!in.hasLink ())
        in.setLink (0, Cell (&m_graph.mkNode (), 0));
      // create cell for the read value and point it to where the link points to
      Cell &c = m_graph.mkCell (I);
      c.pointTo (in.getLink ());
    }
  }
  
  void IntraBlockBuilder::visitCallSite (CallSite CS)
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

    Instruction *inst = CS.getInstruction ();
    
    if (inst && !isSkip (*inst))
    {
      Cell &c = m_graph.mkCell (*inst);
      c.pointTo (m_graph.mkNode (), 0);
      // TODO: mark c as external if it comes from a call to an external function
    }

    
    Value *callee = CS.getCalledValue ()->stripPointerCasts ();
    if (InlineAsm *inasm = dyn_cast<InlineAsm> (callee))
    {
      // TODO: handle inline assembly
    }
    
    // TODO: handle variable argument functions
  }
  
  
  void IntraBlockBuilder::visitMemSetInst (MemSetInst &I)
  {
    // TODO:
    // mark node of I.getDest () as modified
    // can also update size using I.getLength ()
  }
  
  void IntraBlockBuilder::visitMemTransferInst (MemTransferInst &I)
  {
    // TODO: mark I.getDest () is modified, and I.getSource () is read
    assert (m_graph.hasCell (*I.getDest ()));
    assert (m_graph.hasCell (*I.getSource ()));
    // unify the two cells because potentially all bytes of source
    // are copied into dest
    m_graph.mkCell(*I.getDest ()).unify (m_graph.mkCell (*I.getSource ()));
    // TODO: adjust size of I.getLength ()
    // TODO: handle special case when memcpy is used to move non-pointer value only
  }

  void IntraBlockBuilder::visitIntToPtrInst (IntToPtrInst &I)
  {
    // -- only used as a compare. do not needs DSA node
    if (I.hasOneUse () && isa<CmpInst> (*(I.use_begin ()))) return;
    
    dsa::Node &n = m_graph.mkNode ();
    // TODO: mark n appropriately.
    dsa::Cell &c = m_graph.mkCell (I);
    c.pointTo (n, 0);
  }
  
  void IntraBlockBuilder::visitReturnInst(ReturnInst &RI)
  {
    Value *v = RI.getReturnValue ();
    if (!v || isSkip (*v)) return;
    
    dsa::Cell c = m_graph.valueCell (*v);
    if (c.isNull ()) return;

    m_graph.mkRetCell (m_func).pointTo (c);
  }
  
  void IntraBlockBuilder::visitPtrToIntInst (PtrToIntInst &I)
  {
    if (I.hasOneUse () && isa<CmpInst> (*(I.use_begin ()))) return;

    if (I.hasOneUse ())
    {
      Value *v = dyn_cast<Value> (*(I.use_begin ()));
      DenseSet<Value *> seen;
      while (v && v->hasOneUse () && seen.insert (v).second)
      {
        if (isa<LoadInst> (v) || isa<StoreInst> (v) || isa<CallInst> (v)) break;
        v = dyn_cast<Value> (*(v->use_begin ()));
      }
      if (isa<BranchInst> (v)) return;
    }
    assert (m_graph.hasCell (*I.getOperand (0)));
    dsa::Cell c = m_graph.valueCell (*I.getOperand (0));
    if (!c.isNull ())
      /* c->getNode ()->setPtrToInt (true) */;
  }

  
}


namespace seahorn
{
  namespace dsa
  {

    Local::Local () : 
        ModulePass (ID), m_dl (nullptr), m_tli (nullptr) {}

    void Local::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.setPreservesAll ();
    }

    bool Local::runOnModule (Module &M)
    {
      m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      m_tli = &getAnalysis<TargetLibraryInfo> ();
      for (Function &F : M) runOnFunction (F);                
        return false;
    }

    bool Local::runOnFunction (Function &F)
    {
      if (F.isDeclaration () || F.empty ()) return false;
      
      Graph_ptr g = boost::make_shared<Graph> (*m_dl);
      
      // create cells and nodes for formal arguments
      for (Argument &a : F.args ())
        g->mkCell (a).pointTo (g->mkNode (), 0);
      
      std::vector<const BasicBlock *> bbs;
      RevTopoSort (F, bbs);
      boost::reverse (bbs);
      
      IntraBlockBuilder intraBuilder (F, *g, *m_dl, *m_tli);
      InterBlockBuilder interBuilder (*g);
      for (const BasicBlock *bb : bbs)
        intraBuilder.visit (*const_cast<BasicBlock*>(bb));
      for (const BasicBlock *bb : bbs)
        interBuilder.visit (*const_cast<BasicBlock*>(bb));
      
      LOG ("dsa", 
           errs () << "Dsa graph after " << F.getName () << "\n";
           g->write(errs()));
      
      m_graphs [&F] = g;
      return false;
    }

    bool Local::hasGraph (const Function* F) const {
      return (m_graphs.find(F) != m_graphs.end());
    }

    const Graph& Local::getGraph (const Function* F) const {
      auto it = m_graphs.find(F);
      assert (it != m_graphs.end());
      return *(it->second);
    }

    //Pass * createDsaLocalPass () {return new Local ();}
  }
}

char seahorn::dsa::Local::ID = 0;

