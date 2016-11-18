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
  std::pair<uint64_t, uint64_t> computeGepOffset (Type *ptrTy, ArrayRef<Value *> Indicies,
                                                  const DataLayout &dl);
  
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
  
  class BlockBuilderBase
  {
  protected:
    Function &m_func;
    dsa::Graph &m_graph;
    const DataLayout &m_dl;
    const TargetLibraryInfo &m_tli;
    
    
    dsa::Cell valueCell (const Value &v);
    void visitGep (const Value &gep, const Value &base, ArrayRef<Value *> indicies);
    void visitCastIntToPtr (const Value& dest);

    bool isSkip (Value &V)
    {
      if (!V.getType ()->isPointerTy ()) return true;
      // XXX skip if only uses are external functions
      return false;
    }

    static bool isNullConstant (const Value& v)
    {
      const Value *V = v.stripPointerCasts ();

      if (isa<Constant> (V) && cast<Constant> (V)->isNullValue ())
        return true;

      // XXX: some linux device drivers contain instructions gep null, ....
      if (const GetElementPtrInst *Gep = dyn_cast<const GetElementPtrInst>(V))
      {
        const Value &base = *Gep->getPointerOperand ();
        if (const Constant *c = dyn_cast<Constant>(base.stripPointerCasts ())) 
          return c->isNullValue();
      }
      
      return false;
    }
    
  public:
    BlockBuilderBase (Function &func, dsa::Graph &graph,
                      const DataLayout &dl, const TargetLibraryInfo &tli) :
      m_func(func), m_graph(graph), m_dl(dl), m_tli (tli) {}
  };
    
  class InterBlockBuilder : public InstVisitor<InterBlockBuilder>, BlockBuilderBase
  {
    friend class InstVisitor<InterBlockBuilder>;
    
    void visitPHINode (PHINode &PHI);
  public:
    InterBlockBuilder (Function &func, dsa::Graph &graph,
                       const DataLayout &dl, const TargetLibraryInfo &tli) :
      BlockBuilderBase (func, graph, dl, tli) {}
  };
  
  void InterBlockBuilder::visitPHINode (PHINode &PHI)
  {
    if (!PHI.getType ()->isPointerTy ()) return;

    assert (m_graph.hasCell (PHI));
    dsa::Cell &phi = m_graph.mkCell (PHI, dsa::Cell ());
    for (unsigned i = 0, e = PHI.getNumIncomingValues (); i < e; ++i)
    {
      Value &v = *PHI.getIncomingValue (i);
      // -- skip null
      if (isa<Constant> (&v) && cast<Constant> (&v)->isNullValue ()) continue;
      
      dsa::Cell c = valueCell (v);
      assert (!c.isNull ());
      phi.unify (c);
    }
    assert (!phi.isNull ());
  }
  
  class IntraBlockBuilder : public InstVisitor<IntraBlockBuilder>, BlockBuilderBase
  {
    friend class InstVisitor<IntraBlockBuilder>;

    
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
       BlockBuilderBase (func, graph, dl, tli) {}
  };

  
  dsa::Cell BlockBuilderBase::valueCell (const Value &v)
  {
    using namespace dsa;
    assert (v.getType ()->isPointerTy () || v.getType ()->isAggregateType ());
  
    if (isNullConstant (v))
    {
      LOG ("dsa",
           errs () << "WARNING: not handled constant: " << v << "\n";);
      return Cell();
    }
  
    if (m_graph.hasCell (v))
    {
      Cell &c = m_graph.mkCell (v, Cell ());
      assert (!c.isNull ());
      return c;
    }

    if (isa<UndefValue> (&v)) return Cell();
    if (isa<GlobalAlias> (&v)) return valueCell (*cast<GlobalAlias> (&v)->getAliasee ());

    if (isa<ConstantStruct> (&v) || isa<ConstantArray> (&v) ||
        isa<ConstantDataSequential> (&v) || isa<ConstantDataArray> (&v) ||
        isa<ConstantDataVector> (&v))
    {
      // XXX Handle properly
      assert (false);
      return m_graph.mkCell (v, Cell (m_graph.mkNode (), 0));
    }
      
    // -- special case for aggregate types. Cell creation is handled elsewhere
    if (v.getType ()->isAggregateType ()) return Cell ();
  
    if (const ConstantExpr *ce = dyn_cast<const ConstantExpr> (&v))
    {
      if (ce->isCast () && ce->getOperand (0)->getType ()->isPointerTy ())
        return valueCell (*ce->getOperand (0));
      else if (ce->getOpcode () == Instruction::GetElementPtr)
      {
        Value &base = *(ce->getOperand (0));
        SmallVector<Value*, 8> indicies (ce->op_begin () + 1, ce->op_end ());
        visitGep (v, base, indicies);
        assert (m_graph.hasCell (v));
        return m_graph.mkCell (v, Cell());
      } 
      else if (ce->getOpcode () == Instruction::IntToPtr) {
        Value &i = *(ce->getOperand (0));
        visitCastIntToPtr (i);
        assert (m_graph.hasCell (i));
        return m_graph.mkCell (i, Cell());
      }
    }
  
  
    errs () << v << "\n";
    assert(false && "Not handled expression");
    return Cell();
  
  }    
  
  void IntraBlockBuilder::visitInstruction(Instruction &I)
  {
    if (isSkip (I)) return;
    
    m_graph.mkCell (I, dsa::Cell (m_graph.mkNode (), 0));
  }
  
  void IntraBlockBuilder::visitAllocaInst (AllocaInst &AI)
  {
    using namespace seahorn::dsa;
    assert (!m_graph.hasCell (AI));
    Node &n = m_graph.mkNode ();
    // -- record allocation site
    n.addAllocSite(AI);
    // -- mark node as a stack node
    n.setAlloca();
    Cell &res = m_graph.mkCell (AI, Cell (n, 0));
  }
  void IntraBlockBuilder::visitSelectInst(SelectInst &SI)
  {
    using namespace seahorn::dsa;
    if (isSkip (SI)) return;
    
    assert (!m_graph.hasCell (SI));

    Cell thenC = valueCell  (*SI.getOperand (1));
    Cell elseC = valueCell  (*SI.getOperand (2));
    thenC.unify (elseC);
    
    // -- create result cell
    m_graph.mkCell (SI, Cell (thenC, 0));
  }
  
 
  void IntraBlockBuilder::visitLoadInst(LoadInst &LI)
  {
    using namespace seahorn::dsa;

    // -- skip read from NULL
    if (BlockBuilderBase::isNullConstant (*LI.getPointerOperand ()->stripPointerCasts ()))
      return;

    if (!m_graph.hasCell (*LI.getPointerOperand ()->stripPointerCasts ()))
    {
      /// XXX: this is very likely because the pointer operand is the
      /// result of applying one or several gep instructions starting
      /// from NULL. Note that this is undefined behavior but it
      /// occurs in ldv benchmarks.
      if (!isa<ConstantExpr>(LI.getPointerOperand()->stripPointerCasts ()))
	return;
    }
    
    Cell base = valueCell  (*LI.getPointerOperand ()->stripPointerCasts ());
    assert (!base.isNull ());
    base.addType (0, LI.getType ());
    base.setRead();
    // update/create the link
    if (!isSkip (LI)) 
    {
      if (!base.hasLink ())
      {
        Node &n = m_graph.mkNode ();
        base.setLink (0, Cell (&n, 0));
      }
      m_graph.mkCell (LI, base.getLink ());
    }
  }
  
  void IntraBlockBuilder::visitStoreInst(StoreInst &SI)
  {
    using namespace seahorn::dsa;
    
    // -- skip store into NULL
    if (BlockBuilderBase::isNullConstant (*SI.getPointerOperand ()->stripPointerCasts ()))
      return;

    if (!m_graph.hasCell (*SI.getPointerOperand ()->stripPointerCasts ()))
    {
      /// XXX: this is very likely because the pointer operand is the
      /// result of applying one or several gep instructions starting
      /// from NULL. Note that this is undefined behavior but it
      /// occurs in ldv benchmarks.
      if (!isa<ConstantExpr>(SI.getPointerOperand()->stripPointerCasts ()))
	return;
    }
	      
    Cell base = valueCell  (*SI.getPointerOperand ()->stripPointerCasts ());
    assert (!base.isNull ());

    base.setModified();

    // XXX: potentially it is enough to update size only at this point
    base.growSize (0, SI.getValueOperand ()->getType ());
    base.addType (0, SI.getValueOperand ()->getType ());
    
    if (!isSkip (*SI.getValueOperand ()))
    {
      Cell val = valueCell  (*SI.getValueOperand ());
      if (BlockBuilderBase::isNullConstant (*SI.getValueOperand ()))
      {
        // TODO: mark link as possibly pointing to null
      }
      else
      {
        assert (!val.isNull ());
        base.addLink (0, val);
      }
    }
  }

  
  void IntraBlockBuilder::visitBitCastInst(BitCastInst &I)
  {
    if (isSkip (I)) return;

    if (BlockBuilderBase::isNullConstant (*I.getOperand (0)->stripPointerCasts ()))
      return;  // do nothing if null

    dsa::Cell arg = valueCell  (*I.getOperand (0));
    assert (!arg.isNull ());
    m_graph.mkCell (I, arg);
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
          if (arrayIdx < 0)
          {
            errs () << "WARNING: negative GEP index\n";
            // XXX for now, give up as soon as a negative index is found
            // XXX can probably do better. Some negative indexes are positive offsets
            // XXX others are just moving between array cells
            return std::make_pair (0, 1);
          }
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
  
  void BlockBuilderBase::visitGep (const Value &gep,
                                   const Value &ptr, ArrayRef<Value *> indicies)
  {
    // -- skip NULL
    if (const Constant *c = dyn_cast<Constant>(&ptr)) 
      if (c->isNullValue()) return;

    // -- skip NULL
    if (const LoadInst *LI = dyn_cast<LoadInst>(&ptr)) {
      /// XXX: this occurs in several ldv benchmarks
      if (BlockBuilderBase::isNullConstant (*(LI->getPointerOperand ()->stripPointerCasts ())))
	return;
    }
    
    assert (m_graph.hasCell (ptr) || isa<GlobalValue> (&ptr));
    
    // -- empty gep that points directly to the base
    if (gep.stripPointerCasts () == &ptr) return;

    dsa::Cell base = valueCell (ptr);
    assert (!base.isNull ());

    if (m_graph.hasCell (gep)) {
      // gep can have already a cell if it can be stripped to another
      // pointer different from the base.
      if (gep.stripPointerCasts () != &gep) return;
    }

    assert (!m_graph.hasCell (gep));
    dsa::Node *baseNode = base.getNode ();
    if (baseNode->isCollapsed ())
    {
      m_graph.mkCell (gep, dsa::Cell (baseNode, 0));
      return;
    }
    
    auto off = computeGepOffset (ptr.getType (), indicies, m_dl);
    if (off.second)
    {
      // create a node representing the array
      dsa::Node &n = m_graph.mkNode ();
      n.setArraySize (off.second);
      // result of the gep points into that array at the gep offset
      // plus the offset of the base
      m_graph.mkCell (gep, dsa::Cell (n, off.first + base.getOffset ()));
      // finally, unify array with the node of the base 
      n.unify (*baseNode);
    }      
    else
      m_graph.mkCell (gep, dsa::Cell (base, off.first));
  }

  void IntraBlockBuilder::visitGetElementPtrInst(GetElementPtrInst &I)
  {
    Value &ptr = *I.getPointerOperand ();
    SmallVector<Value*, 8> indicies (I.op_begin () + 1, I.op_end ());
    visitGep (I, ptr, indicies);
  }
  
  void IntraBlockBuilder::visitInsertValueInst(InsertValueInst& I)
  {
    assert (I.getAggregateOperand ()->getType () == I.getType ());
    using namespace dsa;

    // make sure that the aggregate has a cell
    Cell op = valueCell  (*I.getAggregateOperand ());
    if (op.isNull ()) {
      dsa::Node &n = m_graph.mkNode ();
      // -- record allocation site
      n.addAllocSite(I);
      // -- mark node as a stack node
      n.setAlloca();
      // -- create a node for the aggregate
      op = m_graph.mkCell (*I.getAggregateOperand (), Cell (n, 0));
    }

    /// JN: I don't understand why we need to create another cell here.
    ///     Should we remove it? 
    Cell &c = m_graph.mkCell (I, op);

    // -- update type record
    Value &v = *I.getInsertedValueOperand ();
    uint64_t offset = computeIndexedOffset (I.getAggregateOperand ()->getType (),
                                            I.getIndices (), m_dl);
    Cell out (op, offset);
    out.growSize (0, v.getType ());
    out.addType (0, v.getType ());
    out.setModified ();

    // -- update link 
    if (!isSkip (v))
    {
      Cell vCell = valueCell  (v);
      assert (!vCell.isNull ());
      out.addLink (0, vCell);
    }
  }
  
  void IntraBlockBuilder::visitExtractValueInst(ExtractValueInst& I)
  {
    using namespace dsa;
    Cell op = valueCell  (*I.getAggregateOperand ());
    if (op.isNull ()) {
      dsa::Node &n = m_graph.mkNode ();
      // -- record allocation site
      n.addAllocSite(I);
      // -- mark node as a stack node
      n.setAlloca();
      op = m_graph.mkCell (*I.getAggregateOperand (), Cell (n, 0));
    }
    
    uint64_t offset = computeIndexedOffset (I.getAggregateOperand ()->getType (),
                                            I.getIndices (), m_dl);
    Cell in (op, offset);

    // -- update type record
    in.addType (0, I.getType ());
    in.setRead ();
    
    if (!isSkip (I))
    {
      // -- create a new node if there is no link at this offset yet
      if (!in.hasLink ()) {
        dsa::Node &n = m_graph.mkNode ();
        in.setLink (0, Cell (&n, 0));
        // -- record allocation site
        n.addAllocSite(I);
        // -- mark node as a stack node
        n.setAlloca();
      }
      // create cell for the read value and point it to where the link points to
      m_graph.mkCell (I, in.getLink ());
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
      // -- record allocation site
      n.addAllocSite(*(CS.getInstruction()));
      // -- mark node as a heap node
      n.setHeap();
      Cell &res = m_graph.mkCell (*CS.getInstruction (), Cell (n, 0));
      return;  
    }

    Instruction *inst = CS.getInstruction ();
    
    if (inst && !isSkip (*inst))
    {
      Cell &c = m_graph.mkCell (*inst, Cell (m_graph.mkNode (), 0));
      if (Function* callee = CS.getCalledFunction ()) {
        if (callee->isDeclaration()) 
        {
          c.getNode()->setExternal();
          // -- treat external function as allocation
          c.getNode ()->addAllocSite (*inst);
          // TODO: many more things can be done to handle external
          // TODO: functions soundly and precisely.  An absolutely
          // safe thing is to merge all arguments with return (with
          // globals) on any external function call. However, this is
          // too aggressive for most cases. More refined analysis can
          // be done using annotations of the external functions (like
          // noalias, does-not-read-memory, etc.). The current
          // solution is okay for now.
        }
      } else {
        // TODO: handle indirect call
      }
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
    dsa::Cell dest = valueCell (*(I.getDest()));
    //assert (!dest.isNull ());    
    if (!dest.isNull ())
      dest.setModified();
    
    // TODO:    
    // can also update size using I.getLength ()
  }
  
  static bool hasNoPointerTy (const llvm::Type *t)
  {
    if (!t) return true;

    if (t->isPointerTy ()) return false;
    if (const StructType *sty = dyn_cast<const StructType>(t))
    {
      for (auto it = sty->element_begin(), end = sty->element_end ();
           it != end; ++it)
        if (!hasNoPointerTy (*it)) return false;
    }
    else if (const SequentialType *seqty = dyn_cast<const SequentialType> (t))
      return hasNoPointerTy (seqty->getElementType ());
    
    return true;
  }
  void IntraBlockBuilder::visitMemTransferInst (MemTransferInst &I)
  {
    // -- trust types, i.e., assume types are not abused by storing
    // -- pointers pointers to other types

    // -- skip copy NULL
    if (isNullConstant (*I.getSource ()))
      return;

    // -- skip copy to an unallocated address
    if (isNullConstant (*I.getDest ()))
      return;

    
    bool TrustTypes = true;
    assert (m_graph.hasCell (*I.getDest ()));
    assert (m_graph.hasCell (*I.getSource ()));

    // unify the two cells because potentially all bytes of source
    // are copied into dest
    dsa::Cell sourceCell = valueCell  (*I.getSource ());
    dsa::Cell destCell = m_graph.mkCell(*I.getDest (), dsa::Cell ());

    assert (I.getSource ()->getType ()->isPointerTy ());
    
    if (TrustTypes &&
        sourceCell.getNode()->links ().size () == 0 &&
        hasNoPointerTy (cast<PointerType> (I.getSource()->getType ())->getElementType ()))
    {
      /* do nothing */
      // no pointers are copied from source to dest, so there is no
      // need to unify them
    }
    else
      destCell.unify (sourceCell);

    sourceCell.setRead();
    destCell.setModified();

    // TODO: can also update size of dest and source using I.getLength ()   

    // TODO: handle special case when memcpy is used to move
    // non-pointer value only
  }

  void BlockBuilderBase::visitCastIntToPtr (const Value& dest) {
    // -- only used as a compare. do not needs DSA node
    if (dest.hasOneUse () && isa<CmpInst> (*(dest.use_begin ()))) return;
    
    dsa::Node &n = m_graph.mkNode ();
    n.setIntToPtr();
    // -- record allocation site
    n.addAllocSite(dest);
    // -- mark node as an alloca node
    n.setAlloca();
    m_graph.mkCell (dest, dsa::Cell (n, 0));

  }

  void IntraBlockBuilder::visitIntToPtrInst (IntToPtrInst &I)
  {
    visitCastIntToPtr (I);
  }
  
  void IntraBlockBuilder::visitReturnInst(ReturnInst &RI)
  {
    Value *v = RI.getReturnValue ();
    if (!v || isSkip (*v)) return;
    
    dsa::Cell c = valueCell  (*v);
    if (c.isNull ()) return;

    m_graph.mkRetCell (m_func, c);
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
    dsa::Cell c = valueCell  (*I.getOperand (0));
    if (!c.isNull ())
      c.getNode()->setPtrToInt ();
  }

  
}


namespace seahorn
{
  namespace dsa
  {

    void LocalAnalysis::runOnFunction (Function &F, dsa::Graph &g)
    {
      // create cells and nodes for formal arguments
      for (Argument &a : F.args ())
        if (a.getType ()->isPointerTy () && !g.hasCell (a)) {
          Node &n = g.mkNode ();
          g.mkCell (a, Cell (n, 0));
          // -- XXX: hook to record allocation site if F is main
          if (F.getName () == "main")
            n.addAllocSite(a);
          // -- mark node as a stack node
          n.setAlloca();
        }
      
      std::vector<const BasicBlock *> bbs;
      RevTopoSort (F, bbs);
      boost::reverse (bbs);
      
      IntraBlockBuilder intraBuilder (F, g, m_dl, m_tli);
      InterBlockBuilder interBuilder (F, g, m_dl, m_tli);
      for (const BasicBlock *bb : bbs)
        intraBuilder.visit (*const_cast<BasicBlock*>(bb));
      for (const BasicBlock *bb : bbs)
        interBuilder.visit (*const_cast<BasicBlock*>(bb));

      g.compress ();

      LOG ("dsa",
           // --- Sanity check
           for (auto &kv: boost::make_iterator_range(g.scalar_begin(),
                                                     g.scalar_end())) 
             if (kv.second->isRead() || kv.second->isModified()) 
               if (kv.second->getNode ()->getAllocSites().empty ()) {
                 errs () << "SCALAR " << *(kv.first) << "\n";
                 errs () << "WARNING: a node has no allocation site\n";
               }
           for (auto &kv: boost::make_iterator_range(g.formal_begin(),
                                                     g.formal_end())) 
             if (kv.second->isRead() || kv.second->isModified()) 
               if (kv.second->getNode ()->getAllocSites ().empty ()) {
                 errs () << "FORMAL " << *(kv.first) << "\n";
                 errs () << "WARNING: a node has no allocation site\n";
               }
           for (auto &kv: boost::make_iterator_range(g.return_begin(),
                                                     g.return_end())) 
             if (kv.second->isRead() || kv.second->isModified()) 
               if (kv.second->getNode ()->getAllocSites ().empty ()) {
                 errs () << "RETURN " << kv.first->getName() << "\n";
                 errs () << "WARNING: a node has no allocation site\n";
               }
           );

      LOG ("dsa-local-graph", 
           errs () << "### Local Dsa graph after " << F.getName () << "\n";
           g.write(errs()));
      
    }
    
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
      
      LOG("progress", errs () << "DSA: " << F.getName () << "\n";);
      
      LocalAnalysis la (*m_dl, *m_tli);
      GraphRef g = std::make_shared<seahorn::dsa::Graph> (*m_dl, m_setFactory);
      la.runOnFunction (F, *g);
      m_graphs [&F] = g;
      return false;
    }

    bool Local::hasGraph (const Function& F) const {
      return (m_graphs.find(&F) != m_graphs.end());
    }

    const Graph& Local::getGraph (const Function& F) const {
      auto it = m_graphs.find(&F);
      assert (it != m_graphs.end());
      return *(it->second);
    }

    //Pass * createDsaLocalPass () {return new Local ();}
  }
}

char seahorn::dsa::Local::ID = 0;

static llvm::RegisterPass<seahorn::dsa::Local> 
X ("sea-dsa-local", "Flow-insensitive, intra-procedural dsa analysis");

