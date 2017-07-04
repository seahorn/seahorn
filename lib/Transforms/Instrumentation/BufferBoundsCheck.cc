#include "seahorn/Transforms/Instrumentation/BufferBoundsCheck.hh"
#include "seahorn/Analysis/CanAccessMemory.hh"
#include "ufo/Passes/NameValues.hpp"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"

#include "boost/format.hpp"

// Seahorn dsa
#include "sea_dsa/DsaAnalysis.hh"
// Llvm dsa
#include "seahorn/Support/DSAInfo.hh"


// To switch between llvm-dsa and sea-dsa
static llvm::cl::opt<bool>
UseSeaDsa("abc-sea-dsa",
          llvm::cl::desc ("Use SeaHorn Dsa analysis"),
          llvm::cl::init (false));

// Notes: Local is obsolete and very incomplete. We keep it for
// comparison with the other encodings just for toy programs.

// BEGIN only for Global
static llvm::cl::opt<unsigned int>
TrackedAllocSite("abc-alloc-site",
        llvm::cl::desc ("Only instrument pointers from this allocation site"),
        llvm::cl::init (0));
static llvm::cl::opt<bool>
InstrumentUnderflow("abc-instrument-underflow",
        llvm::cl::desc ("Add instrumentation for underflow errors"),
        llvm::cl::init (true));
// TODO: InstrumentOverflow
static llvm::cl::opt<bool>
EscapePtr("abc-escape-ptr",
        llvm::cl::desc ("Keep track whether a pointer escapes a function"),
        llvm::cl::init (false));
static llvm::cl::opt<bool>
DerefAssumptions("abc-use-deref",
        llvm::cl::desc ("Use dereferenceable attribute to add assumptions about size arguments"),
        llvm::cl::init (false));
static llvm::cl::opt<bool>
TrackBaseOnly("abc-track-base-only",
        llvm::cl::desc ("Instrument only accesses to base pointers"),
        llvm::cl::init (false));
static llvm::cl::opt<bool>
OnlySurface("abc-surface-only",
        llvm::cl::desc ("Instrument only pointers whose regions do not contain other pointers"),
        llvm::cl::init (false));
// XXX: note that TrackBaseOnly simply ignores GEP instructions while
// StoreBaseOnly checks that only base pointers are stored in memory. 
static llvm::cl::opt<bool>
StoreBaseOnly("abc-store-base-only",
        llvm::cl::desc ("Add instrumentation to check only base pointers are stored"),
        llvm::cl::init (false));
// END only for Global

static llvm::cl::opt<unsigned int>
TrackedDsaNode("abc-dsa-node",
              llvm::cl::desc ("Only instrument pointers within this dsa node"),
              llvm::cl::init (0) /*default all*/);
static llvm::cl::opt<bool>
PositiveAddresses("abc-assume-pos-addr",
                  llvm::cl::desc ("Add assumption that addresses are positive"),
                  llvm::cl::init (false));
static llvm::cl::opt<bool>
InstrumentReads("abc-instrument-reads",
                llvm::cl::desc ("Instrument memory reads"),
                llvm::cl::init (true));
static llvm::cl::opt<bool>
InstrumentWrites("abc-instrument-writes",
                 llvm::cl::desc ("Instrument memory writes"),
                 llvm::cl::init (true));
static llvm::cl::opt<bool>
InstrumentMemIntrinsics("abc-instrument-mem-intrinsics",
                        llvm::cl::desc ("Instrument memcpy, memmove, and memset"),
                        llvm::cl::init (true));
// Consider only user-defined types
static llvm::cl::list<std::string>
InstrumentOnlyType("abc-instrument-only-type",
        llvm::cl::desc ("Only instrument pointers of this user-defined type"),
        llvm::cl::ZeroOrMore);
// Consider only user-defined types
static llvm::cl::list<std::string>
InstrumentExceptType("abc-instrument-except-type",
        llvm::cl::desc ("Instrument all pointers except those from this user-defined type"),
        llvm::cl::ZeroOrMore);

namespace seahorn
{

  // Generic Wwapper for Dsa analysis.  This wrapper allows us to
  // switch from llvm dsa to seahorn dsa
  class DsaWrapper 
  {
  protected:
    llvm::Pass *m_abc; 
    DsaWrapper (llvm::Pass *abc): m_abc (abc) {}
    
  public:
    /* tag only for debugging purposes */
    virtual bool shouldBeTrackedPtr (const llvm::Value &ptr,
				     const llvm::Function& fn, int tag) = 0;
    virtual unsigned int getAllocSiteId (const llvm::Value &ptr) = 0;
    virtual const llvm::Value* getAllocValue (unsigned int id) = 0;    
    virtual const char* getDsaName () const = 0;
  };
  
  
  // A wrapper for seahorn dsa
  class SeaDsa : public DsaWrapper
  { 
    sea_dsa::DsaInfo* m_dsa;
    
    const sea_dsa::Cell*
    getCell (const llvm::Value &ptr, const llvm::Function& fn, int tag) {
      if (!m_dsa)  {
	//errs () << "WARNING ABC: Sea Dsa information not found " << tag << "\n";
	return nullptr; 
      }
      
      sea_dsa::Graph* g = m_dsa->getDsaGraph (fn);
      if (!g) {
	errs () << "WARNING ABC: Sea Dsa graph not found for " << fn.getName () << "\n";
	//<< " " << tag << "\n";
	return nullptr; 
      }
      
      if (!(g->hasCell (ptr))) {
	errs () << "WARNING ABC: Sea Dsa node not found for " << ptr << "\n";
	//<< " " << tag << "\n";
	return nullptr; 
      }
      
      const sea_dsa::Cell &c = g->getCell(ptr);
      return &c;
    }
    
    bool hasSuccessors (const sea_dsa::Cell &c) const {
      const sea_dsa::Node &n = *(c.getNode ());
      return (std::distance (n.links().begin(), n.links().end ()) > 0);
    }
    
    
  public:
    
    SeaDsa(Pass *abc)
      : DsaWrapper(abc),
	m_dsa(&this->m_abc->getAnalysis<sea_dsa::DsaInfoPass>().getDsaInfo()) {}
    
    const char* getDsaName () const { return "SeaHorn Dsa analysis";}
    
    bool shouldBeTrackedPtr (const llvm::Value &ptr, const llvm::Function& fn,
			     int tag)
    {
      auto &v = *(ptr.stripPointerCasts ());
      if (!v.getType()->isPointerTy ()) return false;
      
      // XXX: with GlobalCCallbacks sea global variables are before the abc
	// instrumentation starts.
      if (ptr.getName ().startswith ("sea_")) return false;
      
      const sea_dsa::Cell *c = getCell (v, fn, tag);
      if (!c) return true;
      
      if (OnlySurface && hasSuccessors (*c)) {
	//errs () << "DSA node of " << ptr << " has fields pointing to other nodes.\n";
	return false;
      }
      
      /// XXX: if the dsa analysis is context-sensitive we can have
      /// a node that is not accessed in one function but accessed
      /// in another. Thus, we cannot skip nodes that are not
      /// accessed in the current function.
      
      if (TrackedDsaNode > 0) {
	return (m_dsa->getDsaNodeId (*(c->getNode ())) == TrackedDsaNode);
      }
      
      if (TrackedAllocSite > 0)  {
	if (c->getNode ()->getAllocSites().empty ()) {
	  // errs () << "WARNING ABC: Sea Dsa found node for " << v 
	  //         << " without allocation site " << tag << "\n"
	  //         << *(c->getNode ()) << "\n";
	  
	  // XXX: return false is unsound!
	  // We do this so at least be able to claim "all memory
	  // accesses within dsa nodes with allocation sites are
	  // safe."
	  
	  return false;
	}
        
	if (const Value* AV = m_dsa->getAllocValue (TrackedAllocSite)) {
	  auto const &s = c->getNode ()->getAllocSites ();
	  return (std::find(s.begin(), s.end(), AV) != s.end());
	} else {
	  errs () << "WARNING ABC: allocation site " << TrackedAllocSite
		  << " not understood by Sea Dsa\n"; 
	  return true;
	}
      } 
      return true;
    }
      
    unsigned int getAllocSiteId (const llvm::Value &ptr) 
    { return m_dsa->getAllocSiteId(&ptr); }
    
    const llvm::Value* getAllocValue (unsigned int id)
    { return m_dsa->getAllocValue (id); }
    
  };
  
  // A wrapper for llvm dsa
  class LlvmDsa : public DsaWrapper {
    
    DSAInfo* m_dsa;
    
  public:
    
    LlvmDsa (Pass *abc) : DsaWrapper(abc),  m_dsa(nullptr) 
    { m_dsa = &(abc->getAnalysis<DSAInfo> ()); }
    
    const char* getDsaName () const { return "Llvm Dsa analysis";}
    
    bool shouldBeTrackedPtr (const llvm::Value &ptr,
			     const llvm::Function& fn, int tag) {
      if (!ptr.getType()->isPointerTy ())
	return false;
      
      // XXX: with GlobalCCallbacks sea global variables are before the abc
      // instrumentation starts.
      if (ptr.getName ().startswith ("sea_")) return false;
      
      #ifndef HAVE_DSA
      return true;
      #else
      
      DSGraph* dsg = nullptr;
      DSGraph* gDsg = nullptr;
      if (m_dsa->getDSA ()) {
	dsg = m_dsa->getDSA ()->getDSGraph (fn);
	gDsg = m_dsa->getDSA ()->getGlobalsGraph (); 
      }
      
      if (!dsg || !gDsg) {
	errs () << "WARNING ABC: Llvm Dsa graph not found. This should not happen.\n";
	return true; 
      }
      
      const DSNode* n = dsg->getNodeForValue (&ptr).getNode ();
      if (!n) n = gDsg->getNodeForValue (&ptr).getNode ();
      if (!n)  {
	errs () << "WARNING ABC: Llvm Dsa node not found " 
		<< *(ptr.stripPointerCasts ()) << "\n";
	return true; 
      }
        
      if (!m_dsa->isAccessed (n)) {
        // XXX: we return false because llvm dsa is context-insensitive anyway
	return false;
      } else {
	if (TrackedDsaNode > 0) {
	  return (m_dsa->getDSNodeID (n) == TrackedDsaNode);      
	} else if (TrackedAllocSite > 0) {
	  const Value* v = m_dsa->getAllocValue (TrackedAllocSite);
	  if (!v) {
	    errs () << "WARNING ABC:  Llvm Dsa not value found for allocation site\n";
	    return true;
	  }
	  const DSNode* alloc_n = dsg->getNodeForValue (v).getNode ();
	  return (alloc_n == n);
	} 
      }
      return true;
      #endif 
    }
      
    unsigned int getAllocSiteId (const llvm::Value &ptr) {
      #ifndef HAVE_DSA
      return 0;
      #else
      return m_dsa->getAllocSiteID (&ptr);
      #endif 
    }

    // not implemented
    const llvm::Value* getAllocValue (unsigned int id)
    { return nullptr;}
    
  };
   

  // BEGIN common helpers to all ABC encodings

  // Similar to ObjectSizeOffsetVisitor in MemoryBuiltins but using
  // the dereferenceable attribute
  class WrapperObjectSizeOffsetVisitor
    : public InstVisitor<WrapperObjectSizeOffsetVisitor, SizeOffsetType> {
    
    const DataLayout *DL;
    const TargetLibraryInfo *TLI;
    unsigned IntTyBits;
    APInt Zero;
    SmallPtrSet<Instruction *, 8> SeenInsts;     
    ObjectSizeOffsetVisitor vis;
    
    SizeOffsetType unknown() 
      { return std::make_pair(APInt(), APInt()); }
    
    APInt align(APInt Size, uint64_t Align) {
      const bool RoundToAlign = true; // always true
      if (RoundToAlign && Align)
	return APInt(IntTyBits, RoundUpToAlignment(Size.getZExtValue(), Align));
      return Size;
    }
    
  public:
    
    WrapperObjectSizeOffsetVisitor(const DataLayout *DL, 
				   const TargetLibraryInfo *TLI,
				   LLVMContext &Context) : 
      DL (DL), TLI (TLI), vis (DL, TLI, Context, true) { }
    
    bool knownSize(SizeOffsetType &SizeOffset)
    { return SizeOffset.first.getBitWidth() > 1; }
    
    bool knownOffset(SizeOffsetType &SizeOffset) 
    { return SizeOffset.second.getBitWidth() > 1; }
    
    bool bothKnown(SizeOffsetType &SizeOffset) 
    { return knownSize(SizeOffset) && knownOffset(SizeOffset); }
    
    SizeOffsetType compute(Value *V)  {
      IntTyBits = DL->getPointerTypeSizeInBits(V->getType());
      Zero = APInt::getNullValue(IntTyBits);
      V = V->stripPointerCasts();
      if (Instruction *I = dyn_cast<Instruction>(V)) {
	// If we have already seen this instruction, bail
	// out. Cycles can happen in unreachable code after constant
	// propagation.
	if (!SeenInsts.insert(I).second)
	  return unknown();
	if (GEPOperator *GEP = dyn_cast<GEPOperator>(V))
	  return visitGEPOperator(*GEP);
	if (CallInst* CI = dyn_cast<CallInst> (V)) {
	  // return value of a callsite
	  CallSite CS (CI);
	  unsigned deref_bytes = CS.getDereferenceableBytes(0);
	  if (deref_bytes > 0) {
	    // the size is actually >= deref_bytes so we are
	    // returning a lower bound as the actual size.
	    APInt Size(IntTyBits, deref_bytes);
	    return std::make_pair(align(Size, CS.getParamAlignment(0)), Zero);
	  }
	}
	return vis.compute (V);
      }
      if (Argument *A = dyn_cast<Argument>(V))
	return visitArgument(*A);
      if (isa<ConstantPointerNull>(V))
	return vis.compute(V);
      if (isa<GlobalAlias>(V))
	return vis.compute (V);
      if (isa<GlobalVariable>(V))
	return vis.compute (V);
      if (isa<UndefValue>(V))
	return vis.compute (V);
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
	if (CE->getOpcode() == Instruction::IntToPtr)
	  return unknown(); 
	if (CE->getOpcode() == Instruction::GetElementPtr)
	  return visitGEPOperator(cast<GEPOperator>(*CE));
      }
      return unknown();
    }
    
    SizeOffsetType visitArgument(Argument &A) {
      // no interprocedural analysis is done at the moment
      if (A.hasByValOrInAllocaAttr()) {
	PointerType *PT = cast<PointerType>(A.getType());
	APInt Size(IntTyBits, DL->getTypeAllocSize(PT->getElementType()));
	return std::make_pair(align(Size, A.getParamAlignment()), Zero);
      }
      else {
	uint64_t deref_bytes = A.getDereferenceableBytes ();
	if (deref_bytes > 0) {
	  // the size is actually >= deref_bytes so we are
	  // returning a lower bound as the actual size.
	  APInt Size(IntTyBits, deref_bytes);
	  return std::make_pair(align(Size, A.getParamAlignment()), Zero);
	}
      } 
      return unknown ();
    }
    
    SizeOffsetType visitGEPOperator(GEPOperator &GEP) {
      SizeOffsetType PtrData = compute(GEP.getPointerOperand());
      APInt Offset(IntTyBits, 0);
      if (!bothKnown(PtrData) || !GEP.accumulateConstantOffset(*DL, Offset))
	return unknown();
      return std::make_pair(PtrData.first, PtrData.second + Offset);
    }
    
  }; 
   
  static bool getObjectSize(const Value *Ptr, uint64_t &Size, const DataLayout *DL,
			    const TargetLibraryInfo *TLI, bool RoundToAlign) {
    if (!DL)
      return false;
    WrapperObjectSizeOffsetVisitor Visitor(DL, TLI, Ptr->getContext());
    SizeOffsetType Data = Visitor.compute(const_cast<Value*>(Ptr));
    if (!Visitor.bothKnown(Data))
      return false;
    
    APInt ObjSize = Data.first, Offset = Data.second;
    if (Offset.slt(0) || ObjSize.ult(Offset))
      Size = 0; // overflow
    else
      Size = (ObjSize - Offset).getZExtValue();
    return true;
    //return llvm::getObjectSize(Ptr, Size, DL, TLI, RoundToAlign);
  }

  static Value* getArgument (Function *F, unsigned pos) {
    unsigned idx = 0;
    for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E;
	 ++I, idx++) {
      if (idx == pos) return &*I; 
    }
    return nullptr;
  }
  
  static ReturnInst* getReturnInst (Function *F) {
    // Assume there is one single return instruction per function
    for (llvm::BasicBlock& bb : *F) {
      if (ReturnInst *ret = dyn_cast<ReturnInst> (bb.getTerminator ()))
	return ret;
    }
    return nullptr;
  }
  
  static unsigned storageSize (const DataLayout* dl, const llvm::Type *t) {
    return dl->getTypeStoreSize (const_cast<Type*> (t));
  }
  
  static unsigned storageSize (const DataLayout* dl, llvm::Type *t) {
    return dl->getTypeStoreSize (t);
  }
  
  static int getAddrSize (const DataLayout* dl, const Instruction& I) {
    int size = -1; 
    if (const StoreInst * SI = dyn_cast<const StoreInst> (&I)) {
      if (PointerType* PTy = dyn_cast<PointerType> (SI->getPointerOperand ()->getType ()))
	size = (int) storageSize (dl, PTy->getElementType());
    }
    else if (const LoadInst * LI = dyn_cast<const LoadInst> (&I)) {
      if (PointerType* PTy = dyn_cast<PointerType> (LI->getPointerOperand ()->getType ()))
	size = (int) storageSize (dl, PTy->getElementType());
    }
    return size; 
  }
 
  // Return true iff the check can be determined as definitely safe
  // or unsafe statically.
  static bool IsTrivialCheck (const DataLayout* dl, 
			      const TargetLibraryInfo* tli,
			      const Value* Ptr) {
    
    // Compute the size of the object pointed by Ptr. It also checks
    // for underflow and overflow.
    uint64_t Size;
    if (seahorn::getObjectSize (Ptr, Size, dl, tli, true)){
      // static check
      if (Size == 0) {
	// XXX: this is not true anymore if dereferenceable attribute is used
	errs () << "ArrayBoundsCheck: possible unsafe access to " << *Ptr << "\n";
	return false; // we mark as a non-trivial check.
      }
      return true;
    } 
    return false; 
  }
  
  static bool canEscape (GetElementPtrInst* GEP) {
    for (Use& u: GEP->uses ()) {
      if (isa<ICmpInst> (u.getUser ()))
	continue;
      else if (isa<LoadInst> (u.getUser ()))
	continue;
      else if (StoreInst* SI = dyn_cast<StoreInst> (u.getUser ())) {
	if (SI->getValueOperand () == GEP)
	  return true;
      } else {
	// TODO: any other case where it cannot escape
	return true;
      }
    }
    return false;
  }
  
  static uint64_t fieldOffset (const DataLayout* dl, const StructType *t, 
			       unsigned field) {
    return dl->getStructLayout (const_cast<StructType*>(t))->
      getElementOffset (field);
  }
  
  // Helper to return the next instruction to I
  static Instruction* getNextInst (Instruction* I) {
    if (I->isTerminator ()) return I;
    return I->getParent ()->getInstList ().getNext (I);
  }
  
  static Type* createIntTy (const DataLayout*dl, LLVMContext& ctx) {
    return dl->getIntPtrType (ctx, 0);
  }

  static Type* geti8PtrTy (LLVMContext &ctx) {
    return Type::getInt8Ty (ctx)->getPointerTo ();
  }
  
  static Value* createIntCst (Type* ty, int64_t val) {
    return ConstantInt::get (ty, val);
  }
  
  static Value* createAdd (IRBuilder<> B, const DataLayout*dl,
			   Value *LHS, Value *RHS, 
			   const Twine &Name = "") {
    assert (LHS->getType ()->isIntegerTy () && 
              RHS->getType ()->isIntegerTy ());
    Type* IntTy = createIntTy (dl, B.getContext ());
    Value *LHS1 = B.CreateSExtOrBitCast (LHS, IntTy);
    Value *RHS1 = B.CreateSExtOrBitCast (RHS, IntTy);
    return  B.CreateAdd (LHS1, RHS1, Name);
  }
  
  static Value* createMul (IRBuilder<> B, const DataLayout*dl, 
			   Value *LHS, unsigned RHS, 
			   const Twine &Name = "") {
    assert (LHS->getType ()->isIntegerTy ());
    Type* IntTy = createIntTy (dl, B.getContext ());
    Value* LHS1 = B.CreateSExtOrBitCast (LHS, IntTy );
    return  B.CreateMul (LHS1, 
			 createIntCst (IntTy, RHS),
			 Name);
  }
  
  static Value* createLoad(IRBuilder<> B, Value *Ptr, 
			   const DataLayout* dl,
			   const char *Name = "") {
    return B.CreateAlignedLoad (Ptr, 
				dl->getABITypeAlignment (Ptr->getType ()), 
				Name);
  }
  
  static Value* createStore(IRBuilder<> B, Value* Val, Value *Ptr, 
			    const DataLayout* dl) {
    return B.CreateAlignedStore (Val, Ptr, 
				 dl->getABITypeAlignment (Ptr->getType ()));
  }
  
  static Value* createNullCst (LLVMContext &ctx) {
    return ConstantPointerNull::get (cast<PointerType> (geti8PtrTy (ctx)));
  }
  
  static Value* createGlobalInt (const DataLayout*dl, Module& M, 
				 unsigned val, const Twine& Name ="") {
    IntegerType* intTy = cast<IntegerType>(createIntTy (dl, M.getContext ()));
    ConstantInt *Cst = ConstantInt::get(intTy, val);
    GlobalVariable *GV = new GlobalVariable (M, Cst->getType (), 
					     false,  /*non-constant*/
					     GlobalValue::InternalLinkage,
					     Cst);
    GV->setName(Name);
    return GV;
  }

  static Value* createGlobalBool (Module& M, unsigned val, const Twine& Name ="") {
    ConstantInt *Cst = (val ? 
			ConstantInt::getTrue(M.getContext ()): 
			ConstantInt::getFalse(M.getContext ()));
    GlobalVariable *GV = new GlobalVariable (M, Cst->getType (), false,
					     GlobalValue::InternalLinkage,
                                               Cst);
    GV->setName(Name);
    return GV;
  }
  
  static Value* createGlobalPtr(Module& M, const Twine& Name ="") {
    auto NullPtr = cast<ConstantPointerNull>(createNullCst (M.getContext ()));
    GlobalVariable *GV = new GlobalVariable (M, geti8PtrTy (M.getContext ()), 
					     false, /*non-constant*/
					     GlobalValue::InternalLinkage,
					     NullPtr);
    GV->setName(Name);
    return GV;
  }
  
  //! extract offset from gep using llvm machinery
  static Value* computeGepOffset(const DataLayout* dl, IRBuilder<> B, 
				 GetElementPtrInst *gep) {
    
    LLVMContext& ctx = B.getContext ();
    unsigned IntTyBits = dl->getPointerTypeSizeInBits(gep->getType());
    APInt offset(IntTyBits, 0);
    if (gep->accumulateConstantOffset (*dl, offset)){
      return createIntCst (createIntTy (dl, ctx), offset.getSExtValue ());       
    } else {
      return EmitGEPOffset (&B, *dl, gep, true);
    }
  }
  
  // //! extract offset from gep
  // static Value* computeGepOffset(const DataLayout* dl, IRBuilder<> B, 
  //                                GetElementPtrInst *gep) {
  //   SmallVector<Value*, 4> ps;
  //   SmallVector<Type*, 4> ts;
  //   gep_type_iterator typeIt = gep_type_begin (*gep);
  //   for (unsigned i = 1; i < gep->getNumOperands (); ++i, ++typeIt) {
  //     ps.push_back (gep->getOperand (i));
  //     ts.push_back (*typeIt);
  //   }
  
  //   Type* IntTy = createIntTy (dl, B.getContext ());
  //   Value* base = createIntCst (IntTy, 0);
  //   Value* curVal = base;
  
  //   for (unsigned i = 0; i < ps.size (); ++i) {
  //     if (const StructType *st = dyn_cast<StructType> (ts [i])) {
  //       if (const ConstantInt *ci = dyn_cast<ConstantInt> (ps [i])) {
  //         uint64_t off = fieldOffset (dl, st, ci->getZExtValue ());
  //         curVal = createAdd(B, dl, 
  //                                 curVal, 
  //                                 createIntCst (IntTy, off));
  //       }
  //       else assert (false);
  //     }
  //     else if (SequentialType *seqt = dyn_cast<SequentialType> (ts [i]))
  //     { // arrays, pointers, and vectors
  //       unsigned sz = storageSize (dl, seqt->getElementType ());
  //       Value *lhs = curVal;
  //       Value *rhs = createMul (B, dl, ps[i], sz);
  //       curVal = createAdd (B, dl, lhs, rhs); 
  //     }
  //   } 
  //   return curVal;
  // }
  
  static void updateCallGraph(CallGraph* cg, Function* caller, CallInst* callee) {
    if (cg) {
      (*cg)[caller]->addCalledFunction (CallSite (callee),
					(*cg)[callee->getCalledFunction ()]);
    }
  } 
  
  static Type* stripPointerType (Type* Ty) {
    if (!Ty->isPointerTy ()) return Ty;
    SequentialType * STy = cast<SequentialType> (Ty);
    return stripPointerType (STy->getElementType());
  }

  static bool isInterestingType (Type* Ty) {
    // XXX: do not enforce Ty is a pointer, otherwise allocation of
    // arrays will be ignored.
    //if (!Ty->isPointerTy ()) return false;
    
    if (InstrumentOnlyType.begin () == InstrumentOnlyType.end () &&
         InstrumentExceptType.begin () == InstrumentExceptType.end ()) {
      //errs () << "Instrumented type " << *Ty << "\n";
      return true;
    }
     
    Ty = stripPointerType (Ty);
    
    if (InstrumentExceptType.begin () != InstrumentExceptType.end ()) {
      if (!Ty->isStructTy ()) return true;
      std::string name = Ty->getStructName().str();
      bool res = (std::find(InstrumentExceptType.begin(),
			    InstrumentExceptType.end(),name) != 
		  InstrumentExceptType.end());
      if (res) return false;  
    }
    
    if (InstrumentOnlyType.begin () != InstrumentOnlyType.end ()) {
      if (!Ty->isStructTy ()) return false;
      std::string name = Ty->getStructName().str();
      bool res = (std::find(InstrumentOnlyType.begin(),
			    InstrumentOnlyType.end(),name) != 
		  InstrumentOnlyType.end());
      if (!res) return false;
    }
    
    //errs () << "Instrumented type " << *Ty << "\n";
    return true;
  }
  
  // Check if we want (and can) handle this alloca.
  static bool isInterestingAlloca(const DataLayout* DL, AllocaInst &AI) {
    if (!AI.getAllocatedType()->isSized()) return false;
    
    // alloca() may be called with 0 size, ignore it.
    Type *Ty = AI.getAllocatedType();
    
    if (!isInterestingType (Ty)) return false;
    
    uint64_t SizeInBytes = DL->getTypeAllocSize(Ty);
    return (SizeInBytes > 0);
  }
  

  static Value *isInterestingMemoryAccess(Instruction *I,
					  bool *IsWrite,
					  unsigned *Alignment) {
    
    if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
      if (!InstrumentReads) return nullptr;
      if (!isInterestingType (LI->getPointerOperand()->getType())) return nullptr;
      
      *IsWrite = false;
      *Alignment = LI->getAlignment();
      return LI->getPointerOperand();
    }
    if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
      if (!InstrumentWrites) return nullptr;
      if (!isInterestingType (SI->getPointerOperand()->getType())) return nullptr;
      
      *IsWrite = true;
      *Alignment = SI->getAlignment();
      return SI->getPointerOperand();
    }
    return nullptr;
  }
  // END common helpers to all ABC encodings

  
  // TODO: update the call graph for Local
  Value* Local::lookupSize (const Value* ptr)
  {
    auto it = m_sizes.find (ptr);
    if (it != m_sizes.end ()) return it->second;
    else return nullptr;
  }

  Value* Local::lookupOffset (const Value* ptr)
  {
    auto it = m_offsets.find (ptr);
    if (it != m_offsets.end ()) return it->second;
    else return nullptr;
  }

  Local::ValuePair Local::findShadowArg (Function *F, const Value *Arg) 
  {
    if (m_orig_arg_size.find (F) == m_orig_arg_size.end ()) {
      return ValuePair (nullptr,nullptr);
    }
      
    size_t shadow_idx = m_orig_arg_size [F];
    Function::arg_iterator AI = F->arg_begin();
    for (size_t idx = 0 ; idx < m_orig_arg_size [F] ; ++AI, idx++) {
      const Value* formalPar = &*AI;
      if (formalPar == Arg) {
        Value* shadowOffset = getArgument (F, shadow_idx);
        Value* shadowSize   = getArgument (F, shadow_idx+1);
        assert (shadowOffset && shadowSize);
        return ValuePair (shadowOffset, shadowSize);
      }
      
      if (IsShadowableType (formalPar->getType ()))
        shadow_idx += 2;
    }
    return ValuePair (nullptr,nullptr);
  }

  Local::StoreInstPair Local::findShadowRet (Function *F) {
    return m_ret_shadows [F];
  }

  bool Local::IsShadowableFunction (const Function &F) const  
  { 
    auto it = m_orig_arg_size.find (&F);
    if (it == m_orig_arg_size.end ()) return false;
    return (F.arg_size () > it->second);
    //return (m_orig_arg_size.find (&F) != m_orig_arg_size.end ());
  }

  bool Local::IsShadowableType (Type * ty) const 
  { return ty->isPointerTy (); } 
    
  // return the number of original arguments before the pass added
  // shadow parameters
  size_t Local::getOrigArgSize (const Function &F) {
    assert (IsShadowableFunction (F));
    return m_orig_arg_size [&F];
  }
    
  // For each function parameter for which we want to propagate its
  // offset and size we add two more *undefined* function parameters
  // for placeholding its offset and size which will be filled out
  // later.
  bool Local::addFunShadowParams (Function *F, LLVMContext &ctx) {  
    if (F->isDeclaration ()) return false;

    if (F->getName ().equals ("main")) return false;

    // TODO: relax this case
    if (F->hasAddressTaken ()) return false;
    // TODO: relax this case
    const FunctionType *FTy = F->getFunctionType ();
    if (FTy->isVarArg ()) return false;

    CanAccessMemory &CM = getAnalysis<CanAccessMemory> ();
    if (!CM.canAccess(F)) return false;

    // copy params
    std::vector<llvm::Type*> ParamsTy (FTy->param_begin (), FTy->param_end ());
    // XXX: I use string because StringRef and Twine should not be
    //      stored.
    std::vector<std::string> NewNames;
    Function::arg_iterator FAI = F->arg_begin();
    for(FunctionType::param_iterator I =  FTy->param_begin (),             
            E = FTy->param_end (); I!=E; ++I, ++FAI)  {
      Type *PTy = *I;
      if (IsShadowableType (PTy)) {
        ParamsTy.push_back (m_IntPtrTy);
        Twine offset_name = FAI->getName () + ".shadow.offset";
        NewNames.push_back (offset_name.str ());
        ParamsTy.push_back (m_IntPtrTy);
        Twine size_name = FAI->getName () + ".shadow.size";
        NewNames.push_back (size_name.str ());
      }
    }
    // create function type
    Type *RetTy = F->getReturnType ();
    FunctionType *NFTy = FunctionType::get (RetTy, 
                                            ArrayRef<llvm::Type*> (ParamsTy), 
                                            FTy->isVarArg ());

    // create new function 
    Function *NF = Function::Create (NFTy, F->getLinkage ());
    NF->copyAttributesFrom(F);
    F->getParent ()->getFunctionList ().insert(F, NF);
    NF->takeName (F);

    //m_orig_arg_size [NF] = F->arg_size ();
    assert (m_orig_arg_size.find (NF) == m_orig_arg_size.end ());
    m_orig_arg_size.insert (std::make_pair (NF, F->arg_size ()));

    // new parameter names
    unsigned idx=0;
    for(Function::arg_iterator I = NF->arg_begin(), E = NF->arg_end(); 
        I != E; ++I, idx++) {
      if (idx >= F->arg_size ()) {
        Value* newParam = &*I;
        newParam->setName (NewNames [idx - F->arg_size ()]);
      }
    }
    
    ValueToValueMapTy ValueMap;
    Function::arg_iterator DI = NF->arg_begin();
    for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end();
         I != E; ++I, ++DI)  {
      DI->setName(I->getName());  // Copy the name over.
      // Add a mapping to our mapping.
      ValueMap[I] = DI;
    }
    
    SmallVector<ReturnInst*, 8> Returns; // Ignore returns.
    CloneFunctionInto (NF, F, ValueMap, false, Returns);

    IRBuilder<> B (ctx);

    // placeholders for the variables that will feed the shadow
    // variables for the return instruction of the function
    if (IsShadowableType (RetTy)) {
      ReturnInst* ret = getReturnInst (NF);   
      B.SetInsertPoint (ret);

      // StoreInst* SI_Off = 
      //     B.CreateAlignedStore (UndefValue::get (m_IntPtrTy), 
      //                           m_ret_offset,
      //                           m_dl->getABITypeAlignment (m_ret_offset->getType ())); 

      // StoreInst* SI_Size = 
      //     B.CreateAlignedStore (UndefValue::get (m_IntPtrTy), 
      //                           m_ret_size,
      //                           m_dl->getABITypeAlignment (m_ret_size->getType ())); 

      StoreInst* SI_Off =  B.CreateStore (UndefValue::get (m_IntPtrTy), m_ret_offset); 
      StoreInst* SI_Size = B.CreateStore (UndefValue::get (m_IntPtrTy), m_ret_size);

      m_ret_shadows [NF] = std::make_pair (SI_Off,SI_Size);
    }

    // Replace all callers
    while (!F->use_empty ()) {
      // here we know all uses are call instructions
      CallSite CS (cast<Value>(F->user_back ()));

      Instruction *Call = CS.getInstruction ();
      // Copy the existing arguments
      std::vector <Value*> Args;
      Args.reserve (CS.arg_size ());
      CallSite::arg_iterator AI = CS.arg_begin ();
      for (unsigned i=0, e=FTy->getNumParams (); i!=e ; ++i, ++AI)
        Args.push_back (*AI);

      B.SetInsertPoint (Call);

      // insert placeholders for new arguments
      unsigned added_new_args = NF->arg_size () - F->arg_size();
      for(unsigned i=0; i < added_new_args ; i++)
        Args.push_back (UndefValue::get (m_IntPtrTy)); // for shadow formal parameters

      // create new call 
      Instruction *New = B.CreateCall (NF, ArrayRef<Value*> (Args));
      cast<CallInst>(New)->setCallingConv (CS.getCallingConv ());
      cast<CallInst>(New)->setAttributes (CS.getAttributes ());
      if (cast<CallInst>(Call)->isTailCall ())
        cast<CallInst>(New)->setTailCall ();
      
      if (Call->hasName ())
        New->takeName (Call);

      // Replace all the uses of the old call
      Call->replaceAllUsesWith (New);
      
      // Remove the old call
      Call->eraseFromParent ();

      // wire up shadow actual parameters of the call with the shadow
      // formal parameters of its parent.
      CallSite NCS (const_cast<CallInst*> (cast<CallInst>(New)));

      size_t  orig_arg_size = m_orig_arg_size [NCS.getCalledFunction ()];
      for (unsigned idx = 0, shadow_idx = orig_arg_size; 
           idx < orig_arg_size; idx++) {
        const Value* ArgPtr = NCS.getArgument (idx);
        if (IsShadowableType (ArgPtr->getType ())) {
          ValuePair shadow_pars = 
              findShadowArg (New->getParent ()->getParent(), ArgPtr);
          if (shadow_pars.first && shadow_pars.second) {
            NCS.setArgument(shadow_idx,   shadow_pars.first);
            NCS.setArgument(shadow_idx+1, shadow_pars.second); 
          }
          shadow_idx +=2;
        }
      }
    }

    // -- Do not try to remove because others could have a pointer to
    //    the function (e.g., callgraph).
    // F->eraseFromParent ();

    return true;
  } 
  
  void Local::resolvePHIUsers (const Value *v, 
                              DenseMap <const Value*, Value*>& m_table) {
    // resolve phi incoming values that were marked as undef
    for (Value::const_use_iterator it = v->use_begin(), et = v->use_end (); it!=et; ++it) {
      if (const PHINode *PHI = dyn_cast<PHINode> (*it)) {
        Value * ValShadow = m_table [*it];
        if (!ValShadow) continue;

        if (PHINode *PHIShadow = dyn_cast<PHINode> (ValShadow)) {
          for (unsigned i=0; i < PHI->getNumIncomingValues (); i++) {
            if (PHI->getIncomingValue (i) == v && 
                ( ( i >= PHIShadow->getNumIncomingValues ()) ||
                  PHIShadow->getIncomingValue (i) == UndefValue::get (m_IntPtrTy))) {
              PHIShadow->setIncomingValue (i, m_table [v]);
            }
          }
        }        
      }
    }
  }

  void Local::instrumentGepOffset(IRBuilder<> B, Instruction* insertPoint,
                                 const GetElementPtrInst *gep) {
    SmallVector<const Value*, 4> ps;
    SmallVector<const Type*, 4> ts;
    gep_type_iterator typeIt = gep_type_begin (*gep);
    for (unsigned i = 1; i < gep->getNumOperands (); ++i, ++typeIt) {
      ps.push_back (gep->getOperand (i));
      ts.push_back (*typeIt);
    }

    const Value *base = gep->getPointerOperand ();    
    Value *gepBaseOff = m_offsets [base];

    if (!gepBaseOff)
      return;

    B.SetInsertPoint(insertPoint);
    Value* curVal = gepBaseOff;
    for (unsigned i = 0; i < ps.size (); ++i) {
      if (const StructType *st = dyn_cast<const StructType> (ts [i])) {
        if (const ConstantInt *ci = dyn_cast<const ConstantInt> (ps [i])) {
          uint64_t off = fieldOffset (m_dl, st, ci->getZExtValue ());
          curVal = createAdd (B, m_dl, curVal, 
                                   createIntCst (m_IntPtrTy, off));
        }
        else assert (false);
      }
      else if (const SequentialType *seqt = dyn_cast<const SequentialType> (ts [i])) {
        // arrays, pointers, and vectors
        unsigned sz = storageSize (m_dl, seqt->getElementType ());
        Value *LHS = curVal;
        Value *RHS = createMul (B, m_dl, const_cast<Value*> (ps[i]), sz);
        curVal = createAdd (B, m_dl, LHS, RHS); 
      }
    } 
    m_offsets [gep] = curVal;                                   
    resolvePHIUsers (gep, m_offsets);
  }

  /*
    This instruments the offset and size of ptr by inserting
    arithmetic instructions. We instrument ptr as long as it follows a
    sequence of instructions with this grammar:

    Ptr = globalVariable | alloca | malloc | load | inttoptr | formal param | return |
          (getElementPtr (Ptr) | bitcast (Ptr) | phiNode (Ptr) ... (Ptr) )*  

   */
  void Local::instrumentSizeAndOffsetPtrRec (Function *F, IRBuilder<> B, 
                                            Instruction* insertPoint, 
                                            const Value * ptr,
                                            ValueSet &visited) {

    if (visited.find(ptr) != visited.end ())  return;
    visited.insert (ptr);
    
    /// recursive cases 

    if (const BitCastInst *Bc = dyn_cast<BitCastInst> (ptr)) {
      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (Bc));
      instrumentSizeAndOffsetPtrRec (F, B, insertPoint, 
                                     Bc->getOperand (0),
                                     visited);
      B.SetInsertPoint(insertPoint);
      if (Value* shadowBcOpOff = lookupOffset(Bc->getOperand (0)))
        m_offsets [ptr] = shadowBcOpOff;
      if (Value* shadowBcOpSize = lookupSize(Bc->getOperand (0)))
        m_sizes [ptr] = shadowBcOpSize;

      return;
    }

    if (const GetElementPtrInst *Gep = dyn_cast<GetElementPtrInst> (ptr)) {
      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (Gep));
      instrumentSizeAndOffsetPtrRec (F, B, insertPoint, 
                                     Gep->getPointerOperand (),
                                     visited);
      
      B.SetInsertPoint(insertPoint);
      instrumentGepOffset(B, insertPoint, Gep);
      if (Value* shadowGepOpSize = lookupSize(Gep->getPointerOperand ())) {
        m_sizes [ptr] = shadowGepOpSize;
        resolvePHIUsers (ptr, m_sizes);
      }
      return;
    }

    if (const PHINode *PHI = dyn_cast<PHINode> (ptr)) {
      Instruction *insertPoint = const_cast<Instruction*> (cast<Instruction> (PHI));
      PHINode* shadowPHINodeOff = 
          PHINode::Create (m_IntPtrTy, PHI->getNumIncomingValues (), 
                           ((ptr->hasName ()) ? 
                            ptr->getName () + ".shadow.offset" : ""),
                           insertPoint);
      PHINode* shadowPHINodeSize = 
          PHINode::Create (m_IntPtrTy, PHI->getNumIncomingValues (), 
                           ((ptr->hasName ()) ? 
                            ptr->getName () + ".shadow.size" : ""),
                           insertPoint);

      for (unsigned i=0; i < PHI->getNumIncomingValues (); i++) {
        // placeholder for now
        shadowPHINodeOff->addIncoming (UndefValue::get (m_IntPtrTy), 
                                       PHI->getIncomingBlock (i));
        shadowPHINodeSize->addIncoming (UndefValue::get (m_IntPtrTy), 
                                        PHI->getIncomingBlock (i));
      }

      
      m_offsets [ptr] = shadowPHINodeOff;
      m_sizes [ptr] = shadowPHINodeSize;

      for (unsigned i=0; i < PHI->getNumIncomingValues (); i++) {
        Instruction *insertPoint = 
            dyn_cast<Instruction> (PHI->getIncomingValue (i)); 
        if (!insertPoint)
          insertPoint = PHI->getIncomingBlock (i)->getFirstNonPHI ();
        instrumentSizeAndOffsetPtrRec (F, B, insertPoint, 
                                       PHI->getIncomingValue (i),
                                       visited);
        if (Value* shadowPHIValOff = lookupOffset(PHI->getIncomingValue (i)))
          shadowPHINodeOff->setIncomingValue (i, shadowPHIValOff);
        if (Value* shadowPHIValSize = lookupSize(PHI->getIncomingValue (i)))
          shadowPHINodeSize->setIncomingValue (i, shadowPHIValSize);
      }

      return;
    }

    /// base cases
    if (isa<AllocaInst> (ptr) || isa<GlobalVariable> (ptr) || 
        isa<LoadInst> (ptr) || isAllocationFn (ptr, m_tli, true)) {
      // Here we can handle the load instruction only for simple cases
      // (eg. if the pointer is a global variable)
      uint64_t Size;
      if (seahorn::getObjectSize(ptr, Size, m_dl, m_tli, true)) {
        m_offsets [ptr] = ConstantInt::get (m_IntPtrTy, 0);
        m_sizes [ptr] = ConstantInt::get (m_IntPtrTy, Size);
        return;
      } 

      if (const AllocaInst *AI = dyn_cast<AllocaInst> (ptr))  {
        Value *nElems = const_cast<Value*> (AI->getArraySize ()); // number of elements
        const Type* ty = AI->getAllocatedType (); // size of the allocated type
        unsigned ty_size = storageSize (m_dl, ty);
        Value* size = nullptr;
        B.SetInsertPoint (insertPoint);
        if (ty_size == 1) 
          size = nElems;
        else 
          size = createMul (B, m_dl, nElems, ty_size, "alloca_size");
        m_offsets [ptr] = ConstantInt::get (m_IntPtrTy, 0);
        m_sizes [ptr] = B.CreateZExtOrTrunc (size, m_IntPtrTy);
        return;
      }
      else if (const CallInst * MallocInst = extractMallocCall (ptr ,m_tli)) {
        if (MallocInst->getNumArgOperands () == 1) {
          Value *size = MallocInst->getArgOperand(0);
          if (size->getType ()->isIntegerTy ()) {
            B.SetInsertPoint(insertPoint);
            m_offsets [ptr] = ConstantInt::get (m_IntPtrTy, 0);
            m_sizes [ptr] = B.CreateZExtOrTrunc (size, m_IntPtrTy);
            return;
          }
        }
      }     
    }

    if (isa<IntToPtrInst> (ptr))
    { // TODO
      return;
    }
    
    if (isa<LoadInst> (ptr))
    { // TODO
      return;
    }
    
    /// ptr is the return value of a call site      
    if (const CallInst *CI = dyn_cast<CallInst> (ptr)) {
      CallSite CS (const_cast<CallInst*> (CI));
      Function *cf = CS.getCalledFunction ();      
      if (cf && IsShadowableFunction (*cf)) {
        B.SetInsertPoint(const_cast<CallInst*> (CI)); //just before CI
        auto it = B.GetInsertPoint ();
        ++it; // just after CI
        B.SetInsertPoint (const_cast<llvm::BasicBlock*>(CI->getParent ()), it);

        // m_offsets [ptr] = 
        //     B.CreateAlignedLoad (m_ret_offset,
        //                          m_dl->getABITypeAlignment (m_ret_offset->getType ())); 

        // m_sizes [ptr] = 
        //     B.CreateAlignedLoad (m_ret_size,
        //                          m_dl->getABITypeAlignment (m_ret_size->getType ())); 

        m_offsets [ptr] = B.CreateLoad (m_ret_offset); 
        m_sizes [ptr] = B.CreateLoad (m_ret_size); 
        return;
      }
    }
    
    /// if ptr is a function formal parameter
    auto p =  findShadowArg (F, ptr);
    Value* shadowPtrOff =  p.first;
    Value* shadowPtrSize = p.second;
    if (shadowPtrOff && shadowPtrSize) {
      m_offsets [ptr] = shadowPtrOff;
      m_sizes [ptr] = shadowPtrSize;      
      return;
    }
  }


  void Local::instrumentSizeAndOffsetPtr (Function *F, IRBuilder<> B, 
                                         Instruction* insertPoint, 
                                         const Value * ptr) {
    ValueSet visited;
    instrumentSizeAndOffsetPtrRec (F, B, insertPoint, ptr, visited);
  }

  //! Instrument check for memory accesses
  bool Local::instrumentCheck (Function& F, IRBuilder<> B, 
                              Instruction& inst, 
                              const Value& ptr, Value* len) {
    // Figure out offset and size
    instrumentSizeAndOffsetPtr (&F, B, &inst, &ptr);
    Value *ptrSize   = m_sizes [&ptr];
    Value *ptrOffset = m_offsets [&ptr];

    if (!ptrSize || !ptrOffset) {
      m_checks_unable++;
      return false;
    }

    // Create error blocks
    LLVMContext& ctx = B.getContext ();
    BasicBlock* err_under_bb = BasicBlock::Create(ctx, "underflow_error_bb", &F);
    BasicBlock* err_over_bb = BasicBlock::Create(ctx, "overflow_error_bb", &F);

    B.SetInsertPoint (err_under_bb);
    CallInst* ci_under = B.CreateCall (m_errorFn);
    ci_under->setDebugLoc (inst.getDebugLoc ());
    B.CreateUnreachable ();
    
    B.SetInsertPoint (err_over_bb);
    CallInst* ci_over = B.CreateCall (m_errorFn);
    ci_over->setDebugLoc (inst.getDebugLoc ());
    B.CreateUnreachable ();
    
    
    B.SetInsertPoint (&inst);    

    BasicBlock *OldBB0 = inst.getParent ();
    BasicBlock *Cont0 = OldBB0->splitBasicBlock(B.GetInsertPoint ());
    OldBB0->getTerminator ()->eraseFromParent ();
    BranchInst::Create (Cont0, OldBB0);
    
    B.SetInsertPoint (Cont0->getFirstNonPHI ());    

    /// --- Underflow: add check offset >= 0 
    Value* Cond_U = B.CreateICmpSGE (ptrOffset, 
                                     ConstantInt::get (m_IntPtrTy, 0),
                                     "buffer_under");

    BasicBlock *OldBB1 = Cont0;
    BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint ());
    OldBB1->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont1, err_under_bb, Cond_U, OldBB1);

    m_checks_added++;
    B.SetInsertPoint (Cont1->getFirstNonPHI ());    

    /// --- Overflow: add check 
    //      offset + addr_sz <= size or offset + len <= size 

    Value *range = nullptr;
    if (len) {
      range = createAdd (B, m_dl, ptrOffset, len);
    } else {
      int addr_sz = getAddrSize (m_dl, inst);
      if (addr_sz < 0) { // This should not happen ...
        report_fatal_error("ABC pass cannot find size of address");
      }
      range = createAdd (B, m_dl, ptrOffset, 
                              createIntCst (m_IntPtrTy, addr_sz));
    }
    
    Value* Cond_O = B.CreateICmpSLE (range, ptrSize, "buffer_over");

    BasicBlock *OldBB2 = Cont1;
    BasicBlock *Cont2 = OldBB2->splitBasicBlock(B.GetInsertPoint ());
    OldBB2->getTerminator ()->eraseFromParent();
    BranchInst::Create (Cont2, err_over_bb, Cond_O, OldBB2);

    m_checks_added++;
    return true;
  }

  bool Local::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;

    std::unique_ptr<DsaWrapper> dsa (new SeaDsa (this));
    if (!UseSeaDsa)
      dsa.reset (new LlvmDsa (this));

    errs () << " --- Using " << dsa->getDsaName () << "\n";

    LLVMContext &ctx = M.getContext ();
    m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
    m_tli = &getAnalysis<TargetLibraryInfo>();

    m_IntPtrTy = m_dl->getIntPtrType (ctx, 0);
    errs () << "intPtrTy is " << *m_IntPtrTy << "\n";

    AttrBuilder AB;
    AB.addAttribute (Attribute::NoReturn);
    AttributeSet as = AttributeSet::get (ctx, 
                                         AttributeSet::FunctionIndex,
                                         AB);
    
    m_errorFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.error",
                                as,
                                Type::getVoidTy (ctx), nullptr));
        
    /* Shadow function parameters */
    std::vector<Function*> funcsToInstrument;
    funcsToInstrument.reserve (std::distance (M.begin (), M.end ()));
    for (Function &F : M) { 
      if (!F.isDeclaration ())
        funcsToInstrument.push_back (&F);
    }
    // Insert shadow global variables for function return values 
    m_ret_offset = createGlobalInt (m_dl, M, 0, "ret.offset");
    m_ret_size = createGlobalInt (m_dl, M, 0, "ret.size");
    for (auto F: funcsToInstrument) {
       addFunShadowParams (F, ctx);
    }

    // TODO: addFunShadowParams invalidates Dsa information since it
    // adds shadow parameters by making new copies of the existing
    // functions and then removing those functions.
    if (TrackedDsaNode != 0) {
      errs () << "WARNING ABC: Dsa is invalidated so we cannot use Dsa info ...\n";
      TrackedDsaNode = 0;
    }
    
    /* Instrument load/store/memcpy/memmove/memset instructions */
    unsigned untracked_dsa_checks = 0;
    std::vector<Instruction*> WorkList;
    for (Function &F : M) {
      
      if (F.isDeclaration ()) continue;
      if (!F.hasName ()) continue; // skip old functions before instrumentation
      
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
        Instruction *I = &*i;
        if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
          Value* ptr = LI->getPointerOperand ();
          if (ptr == m_ret_offset || ptr == m_ret_size) continue;
            
          if (dsa->shouldBeTrackedPtr (*ptr, F, __LINE__))
            WorkList.push_back (I);
          else
            untracked_dsa_checks++; 
          
        } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
          Value* ptr = SI->getPointerOperand ();
          if (ptr == m_ret_offset || ptr == m_ret_size) continue;

          if (dsa->shouldBeTrackedPtr (*ptr, F, __LINE__))
            WorkList.push_back (I);
          else
            untracked_dsa_checks++; 
          
        } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
          if (dsa->shouldBeTrackedPtr (*MTI->getDest (), F, __LINE__) || 
              dsa->shouldBeTrackedPtr (*MTI->getSource (), F, __LINE__))
            WorkList.push_back (I);
          else
            untracked_dsa_checks+=2;
        } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
          Value* ptr = MSI->getDest ();
          if (dsa->shouldBeTrackedPtr (*ptr, F, __LINE__))
            WorkList.push_back (I);            
          else
            untracked_dsa_checks++; 
          
        } else if (isa<CallInst> (I) || isa<ReturnInst> (I)) {
          WorkList.push_back(I);
        }
      }
    }

    IRBuilder<> B (ctx);

    for (auto inst: WorkList) {
      Function* F = inst->getParent()->getParent();
      // make sure we do first these two cases before visiting
      // CallInst
      if (MemTransferInst *MTI = dyn_cast<MemTransferInst> (inst)) {
        m_mem_accesses+=2;
        Value* DestPtr = MTI->getDest ();
        Value* SrcPtr = MTI->getSource ();
        instrumentCheck (*F, B, *inst, *SrcPtr, MTI->getLength ());           
        instrumentCheck (*F, B, *inst, *DestPtr, MTI->getLength ());           
      }
      else if (MemSetInst *MSI = dyn_cast<MemSetInst> (inst)) {
        m_mem_accesses++;
        Value* DestPtr = MSI->getDest ();
        instrumentCheck (*F, B, *inst, *DestPtr, MSI->getLength ());           
      }
      else if (const CallInst *CI = dyn_cast<CallInst> (inst)) {
        CallSite CS (const_cast<CallInst*> (CI));
        const Function *cf = CS.getCalledFunction ();
        if (cf) {
          if (cf->isIntrinsic ()) continue;
          // Resolving the shadow offsets and sizes which are
          // actual parameters of a function call
          // At this point F has this form:
          //
          // q = foo (p,...,_,_,&q.off,&q.size);
          //
          // The placeholders are filled out with the shadow
          // variables corresponding to p.
          if (IsShadowableFunction (*cf)) {
            size_t orig_arg_size = getOrigArgSize (*cf);
            unsigned shadow_idx = orig_arg_size;
            for (size_t idx= 0; idx < orig_arg_size; idx++) {
              const Value* ArgPtr = CS.getArgument (idx);
              // this could be a symptom of a bug
              if (isa<UndefValue> (ArgPtr) || isa<ConstantPointerNull> (ArgPtr))
                continue;
              if (IsShadowableType (ArgPtr->getType ())) {
                instrumentSizeAndOffsetPtr (F, B, inst, ArgPtr);                  
                Value *ptrSize   = m_sizes [ArgPtr];
                Value *ptrOffset = m_offsets [ArgPtr];
                if (ptrSize && ptrOffset) {
                  CS.setArgument (shadow_idx, ptrOffset);
                  CS.setArgument (shadow_idx+1, ptrSize);
                }
                shadow_idx +=2;
              }
            }
          }
        }
      }
      else if (const ReturnInst *ret = dyn_cast<ReturnInst> (inst)) {
        if (const Value* retVal = ret->getReturnValue ()) {
          if (IsShadowableType (retVal->getType ())) {
            // Resolving the shadow offset and size of the return
            // value of a function. At this point, F has this form:
            //    ...
            //    g_ret.off = _;
            //    g_ret.size = _;
            //    return p;
            // 
            // The placeholders _ are filled out with the shadow
            // variables associated with the return variable.
            instrumentSizeAndOffsetPtr (F, B, inst, retVal);                  
            Value *ShadowOffset = m_offsets [retVal];
            Value *ShadowSize = m_sizes [retVal];
            if (ShadowOffset && ShadowSize) {
              auto p = findShadowRet (F);
              if (p.first) 
                p.first->setOperand (0, ShadowOffset);
              if (p.second) 
                p.second->setOperand (0, ShadowSize);
            }
          }
        }
      }
      else if (LoadInst *load = dyn_cast<LoadInst> (inst)) {
        Value * Ptr = load->getOperand (0);
        if (Ptr == m_ret_size || Ptr == m_ret_offset) continue;
        
        m_mem_accesses++;
        if (!IsTrivialCheck (m_dl, m_tli, Ptr))  {
          instrumentCheck (*F, B, *inst, *Ptr, nullptr);           
        } else 
          m_trivial_checks++;
      }
      else if (StoreInst *store = dyn_cast<StoreInst> (inst)) {
        Value * Ptr = store->getOperand (1);
        if (Ptr == m_ret_size || Ptr == m_ret_offset) continue;

        m_mem_accesses++;
        if (!IsTrivialCheck (m_dl, m_tli, Ptr)) {
          instrumentCheck (*F, B, *inst, *Ptr, nullptr);           
        } else 
          m_trivial_checks++;
      }
    }
    
    errs () << " ========== ABC  ==========\n"
            << "-- " << m_mem_accesses - m_trivial_checks   
            << " Total number of non-trivial memory reads/writes\n" 
            << "-- " << m_trivial_checks
            << " Total number of trivially safe memory reads/writes (not instrumented)\n"
            << "-- " << m_mem_accesses - m_trivial_checks - m_checks_unable  
            << " Total number of memory reads/writes instrumented\n"
            << "-- " << m_checks_unable
            << " Total number of memory reads/writes NOT instrumented\n"
            << "-- " << m_checks_added    
            << " Total number of added buffer overflow/underflow checks\n";

    if (TrackedDsaNode != 0) {
      errs () << "-- " << untracked_dsa_checks 
              << " Total number of skipped checks because untracked Dsa node\n";
    }

    return true;
  }
    
  void Local::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<seahorn::DSAInfo>();     // run llvm dsa
    AU.addRequired<sea_dsa::DsaInfoPass>(); // run seahorn dsa
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::TargetLibraryInfo>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addRequired<CanAccessMemory> ();
  } 

  char Local::ID = 0;

  static llvm::RegisterPass<Local> 
  X ("abc-local", "Insert array buffer checks using local encoding");


  
  Function& Global::InstVis::
  createNewNondetFn (Module &m, Type &type, unsigned num, std::string prefix) {
    std::string name;
    unsigned c = num;
    
    do
      name = boost::str (boost::format (prefix + "%d") % (c++));
    while (m.getNamedValue (name));
    Function *res = dyn_cast<Function>(m.getOrInsertFunction (name, &type, NULL));
    assert (res);
    if (m_cg) m_cg->getOrInsertFunction (res);
    return *res;
  }
    
  CallInst* Global::InstVis::NonDet (Function* caller) {
    Module &m = *(caller->getParent ());
    auto &nondetFn = createNewNondetFn (m, *m_IntPtrTy, m_nondet_id, "verifier.nondet");
    CallInst *CI = m_B.CreateCall (&nondetFn, "nd");
    updateCallGraph (m_cg, caller, CI);
    return CI;
  }
  
  CallInst* Global::InstVis::NonDetPtr (Function* caller) {
    Type *i8PtrTy = Type::getInt8Ty (m_B.getContext())->getPointerTo ();
    Module &m = *(caller->getParent ());
    auto &nondetPtrFn = createNewNondetFn (m, *i8PtrTy, m_nondet_id, "verifier.nondet_ptr");
    CallInst* CI = m_B.CreateCall (&nondetPtrFn, "nd_ptr");
    updateCallGraph (m_cg, caller, CI);
    return CI;
  }
  
  void Global::InstVis::Assume (Value* cond, Function* F) {
    CallInst* CI = m_B.CreateCall (m_assumeFn, cond);
    updateCallGraph (m_cg, F, CI);
  }
  
  // Add in cur the instruction "br cond, then, error" where error is a
  // new block that contains a call to the error function.
  BasicBlock* Global::InstVis::Assert (Value* cond, BasicBlock* then, BasicBlock* cur, 
                                       Instruction* instToBeChecked, 
                                       const Twine &errorBBName){
    
    BasicBlock* err_bb = 
      BasicBlock::Create(m_B.getContext (), errorBBName, cur->getParent());
    
    m_B.SetInsertPoint (err_bb);
    CallInst* ci = m_B.CreateCall (m_errorFn);
    updateCallGraph (m_cg, cur->getParent (), ci);
    ci->setDebugLoc (instToBeChecked->getDebugLoc ());
    m_B.CreateUnreachable ();
    
    BranchInst::Create (then, err_bb, cond, cur);            
    
    return err_bb;
  }
  
  //! Instrument lhs = gep (base, offset);
  void Global::InstVis::doPtrArith (GetElementPtrInst * gep, 
                                    Instruction* insertPt) {
    /* 
       if (nd () && tracked_ptr && tracked_ptr == base) {
             tracked_ptr = nd (); 
             assume (tracked_ptr == lhs);
             tracked_offset += offset;
             tracked_escaped_ptr = false;
	     }
    */
    
    if (TrackBaseOnly) return;
    
    LLVMContext& ctx = m_B.getContext ();
    BasicBlock* bb = insertPt->getParent ();
    Function* F = bb->getParent ();
    BasicBlock* cont = bb->splitBasicBlock(insertPt);
    
    m_B.SetInsertPoint (bb->getTerminator ());
    /// if (nd () && tracked_ptr && base(gep) == tracked_ptr)
    
    CallInst *nd = NonDet (insertPt->getParent()->getParent());
    Value* condA = m_B.CreateICmpSGE (nd, createIntCst (m_IntPtrTy, 0)); 
    
    Value *vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);
    Value* condB = m_B.CreateICmpSGT(vtracked_ptr, createNullCst (ctx));
    
    Value* base = gep->getPointerOperand ();                                       
    Value* condC = m_B.CreateICmpEQ (vtracked_ptr,
				     m_B.CreateBitOrPointerCast (base, geti8PtrTy (ctx)));
    Value* cond = m_B.CreateAnd (condA, m_B.CreateAnd (condB, condC));
    bb->getTerminator ()->eraseFromParent ();      
    BasicBlock* bb1 = BasicBlock::Create(ctx, "update_ptr_" + gep->getName ()  + "_bb", F);
    BranchInst::Create (bb1, cont, cond, bb);      
    
    m_B.SetInsertPoint (bb1);
    // This code is equivalent to
    //
    //       tracked_ptr = lhs
    //
    // but it tricks the alias analysis to avoid aliasing
    // tracked_ptr and lhs:
    //
    //       tracked_ptr = nd ();
    //       assume (tracked_ptr == lhs)
    CallInst* nd_ptr = NonDetPtr (insertPt->getParent()->getParent());
    createStore (m_B, nd_ptr, m_tracked_ptr, m_dl);      
    Assume (m_B.CreateICmpEQ(nd_ptr, 
			     m_B.CreateBitOrPointerCast (gep, geti8PtrTy (ctx))),
	    insertPt->getParent()->getParent());
    
    /// tracked_offset += n;
    Value* offset = computeGepOffset (m_dl, m_B, gep);    
    createStore (m_B, 
		      createAdd(m_B, m_dl,
				     offset, 
				     createLoad(m_B, m_tracked_offset, m_dl)),
		      m_tracked_offset, m_dl);
    
    if (EscapePtr) {
      /// tracked_escaped_ptr = false
      createStore(m_B, ConstantInt::getFalse(m_B.getContext ()), 
		       m_tracked_escaped_ptr, m_dl);
    }
    
    BranchInst::Create (cont, bb1);
  }
  
  //! Initialization of tracked base, offset, and size.
  void Global::InstVis::doInit (Module& M) {
    /*
      assume (tracked_base > 0);
      assume (tracked_size > 0);
      tracked_ptr = 0;
      tracked_offset = 0;
      tracked_escaped_ptr = false;
    */
    
    Function* main = M.getFunction ("main");
    assert (main);
    m_B.SetInsertPoint (main->getEntryBlock ().getFirstInsertionPt ());
    LLVMContext& ctx = m_B.getContext ();      
    
    // assume (m_tracked_base > 0);
    m_tracked_base = createGlobalPtr (M, "tracked_base");
    CallInst* p1 = NonDetPtr (main);
    Assume (m_B.CreateICmpSGT(p1, 
			      m_B.CreateBitOrPointerCast (createNullCst (ctx), 
							  p1->getType ())), main);
    createStore (m_B, p1, m_tracked_base, m_dl);
    
    // assume (m_tracked_size > 0);
    m_tracked_size = createGlobalInt (m_dl, M, 0, "tracked_size");      
    CallInst *x = NonDet (main);
    Assume (m_B.CreateICmpSGT(x, createIntCst (m_IntPtrTy, 0)), main);
    createStore (m_B, x, m_tracked_size, m_dl);
    
    // m_tracked_ptr = 0
    m_tracked_ptr  = createGlobalPtr ( M, "tracked_ptr");
    createStore (m_B, createNullCst (ctx), m_tracked_ptr, m_dl);
    
    // m_tracked_offset = 0;
    m_tracked_offset = createGlobalInt (m_dl, M, 0, "tracked_offset");
    
    if (EscapePtr) {
      // m_tracked_escaped = false;
      m_tracked_escaped_ptr = createGlobalBool (M, false, "tracked_escaped_ptr");
    }
    
    Instruction * insertPt = m_B.GetInsertPoint ();
    /// Allocation of global variables
    for (auto &GV: M.globals ()) {
      Type *Ty = cast<PointerType>(GV.getType())->getElementType();
      if (!Ty->isSized()) continue;
      if (!GV.hasInitializer()) continue;
      if (globalGeneratedBySeaHorn (&GV)) continue;
      if (!(m_dsa->shouldBeTrackedPtr (GV, *main, __LINE__))) continue;
      if (GV.hasSection()) {
	StringRef Section(GV.getSection());
	// Globals from llvm.metadata aren't emitted, do not instrument them.
	if (Section == "llvm.metadata") continue;
      }
      
      uint64_t size;
      if (seahorn::getObjectSize(&GV, size, m_dl, m_tli, true)) {
	doAllocaSite (&GV, createIntCst (m_IntPtrTy, size), insertPt); 
      }
      else {
	// this should not happen unless the global is external
	errs () << "WARNING ABC: missing allocation site from global " << GV
		<< " because its size cannot be inferred statically.\n";
      }
    }
  }
  
  //! Instrument any allocation site
  void Global::InstVis::doAllocaSite (Value* Ptr,
				      Value* Size /* bytes (null if unknown)*/, 
                                      Instruction* insertPt) {
    /*
      if (!tracked_ptr && p == tracked_base)
          tracked_ptr = nd ();
          assume (tracked_ptr == tracked_base);
          assume (tracked_size == n)
          tracked_offset = 0 
       else { 
          assume (tracked_base + m_tracked_size < p); 
       }
     */
      
    if (TrackedAllocSite > 0) {
      if (m_dsa->getAllocSiteId (*Ptr) == TrackedAllocSite) {
	goto ALLOCA;
      } else {
	// assume (tracked_base + tracked_size < ptr); 
	m_B.SetInsertPoint (insertPt);
	Value* vtracked_size = createLoad(m_B, m_tracked_size, m_dl);
	Value* vtracked_base = createLoad(m_B, m_tracked_base, m_dl);
	Value* vPtr = m_B.CreateBitOrPointerCast (Ptr, geti8PtrTy (m_B.getContext ()));
	
	
	/////
	// it tricks the alias analysis so tracked_base is not marked as
	// an array:
	// Assume (m_B.CreateICmpSLT(m_B.CreateGEP(vtracked_base, vtracked_size), vPtr),
	//        insertPt->getParent()->getParent());
	////
	
	// tmp = nd_ptr ();
	// assume (tmp == base);
	// assume (tmp  + size < p);
	Function* F = insertPt->getParent()->getParent();
	CallInst* nd_ptr = NonDetPtr (F);
	Assume (m_B.CreateICmpEQ(nd_ptr, vtracked_base), F);
	Assume (m_B.CreateICmpSLT(m_B.CreateGEP(nd_ptr, vtracked_size), vPtr), F);      
	
	return;
      }
    }
    
  ALLOCA:
    
    LLVMContext& ctx = m_B.getContext ();
    BasicBlock* bb = insertPt->getParent ();
    Function* F = bb->getParent ();
    BasicBlock *cont = bb->splitBasicBlock(insertPt);
    BasicBlock* alloca_then_bb = 
      BasicBlock::Create(ctx, "allocated_" + Ptr->getName () + "_bb", F);
    BasicBlock* alloca_else_bb = 
      BasicBlock::Create(ctx, "not_allocated_" + Ptr->getName () + "_bb", F);
    
    m_B.SetInsertPoint (bb->getTerminator ());
    Value* vtracked_size = createLoad(m_B, m_tracked_size, m_dl);
    Value* vtracked_base = createLoad(m_B, m_tracked_base, m_dl);
    Value* vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);
    Value* PtrX = m_B.CreateBitOrPointerCast (Ptr, geti8PtrTy (ctx));
    Value* cond = m_B.CreateAnd (m_B.CreateIsNull(vtracked_ptr),
				 m_B.CreateICmpEQ (PtrX, vtracked_base));
    
    bb->getTerminator ()->eraseFromParent ();      
    BranchInst::Create (alloca_then_bb, alloca_else_bb, cond, bb);      
    
    m_B.SetInsertPoint (alloca_then_bb);
    // This code is equivalent to 
    // 
    //      tracked_ptr = tracked_base 
    // 
    // but it tricks the alias analysis to avoid aliasing
    // tracked_ptr and tracked_base:
    // 
    //      tracked_ptr = nd ();
    //      assume (tracked_ptr == tracked_base)
    CallInst* nd_ptr = NonDetPtr (insertPt->getParent()->getParent());
    createStore (m_B, nd_ptr, m_tracked_ptr, m_dl);      
    Assume (m_B.CreateICmpEQ(nd_ptr, vtracked_base), F);
    
    /// assume (tracked_size == n);
    if (Size == nullptr ){
      // If Size is unknown we create a symbolic variable for it and
      // assume its size is greater than zero.
      CallInst* nd_sz = NonDet (F);
      Assume (m_B.CreateICmpSGT(nd_sz, createIntCst (m_IntPtrTy, 0)),F);	
      Assume (m_B.CreateICmpEQ(vtracked_size,
			       m_B.CreateZExtOrTrunc(nd_sz, createIntTy (m_dl, ctx))), F);
      
    } else {
      Assume (m_B.CreateICmpEQ(vtracked_size,
			       m_B.CreateZExtOrTrunc (Size, createIntTy (m_dl, ctx))), F);
    }

                                            
    /// tracked_offset = 0
    createStore (m_B, createIntCst (m_IntPtrTy, 0), 
		      m_tracked_offset, m_dl);
    
    BranchInst::Create (cont, alloca_then_bb);
    
    // assume (tracked_base + tracked_size < p);
    m_B.SetInsertPoint (alloca_else_bb);
    /////
    // it tricks the alias analysis so tracked_base is not marked as
    // an array:
    // Assume (m_B.CreateICmpSLT(m_B.CreateGEP(vtracked_base, vtracked_size), PtrX), F);
    ////
    
    // tmp = nd_ptr ();
    // assume (tmp == base);
    // assume (tmp  + size < p);
    CallInst* nd_ptr1 = NonDetPtr (F);
    Assume (m_B.CreateICmpEQ(nd_ptr1, vtracked_base), F);
    Assume (m_B.CreateICmpSLT(m_B.CreateGEP(nd_ptr1, vtracked_size), PtrX), F);      
    
    BranchInst::Create (cont, alloca_else_bb);
    
  }
  
  //! Instrument a load/store whose pointer is coming from a Gep and
  //! the object has a known size.
  void Global::InstVis::doGepOffsetCheck (GetElementPtrInst* gep, 
                                          uint64_t size, 
                                          Instruction* insertPt) {
    
    /*
      Let gep be an instruction gep (b,o) and s the size of the
      object pointed by b
      
      // overflow
      assert (o + addr_sz <= s); 
      // underflow
      if (b == tracked_base) 
         assert (o >= 0);
      else if (b == tracked_ptr) 
         assert (tracked_offset + o >= 0);
    */
    int addr_sz = getAddrSize (m_dl, *insertPt);
    if (addr_sz < 0) { // this should not happen
      report_fatal_error("ABC pass cannot find size of address");
    }
    
    // -- compute offset and insert it just before the gep instruction
    m_B.SetInsertPoint (gep); 
    Value* voffset = computeGepOffset (m_dl, m_B, gep);
    Value* voffset_addr_sz = createAdd (m_B, m_dl, voffset,
					     createIntCst (m_IntPtrTy, addr_sz),
					     "off.addr_sz");
    
    // -- insertPt is one instruction after the gep instruction
    Value* base = gep->getPointerOperand ();
    LLVMContext& ctx = m_B.getContext ();
    BasicBlock* bb = insertPt->getParent ();
    Function* F = bb->getParent ();
    BasicBlock *cont = bb->splitBasicBlock(insertPt);
    
    BasicBlock* bb1 = BasicBlock::Create(ctx, mkBBName("over_check",base), F);
    BasicBlock* bb2 = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
    
    bb->getTerminator ()->eraseFromParent ();      
    BranchInst::Create (bb1, bb);      
    
    // assert (offset + addr_sz <= size);     
    m_B.SetInsertPoint (bb1);                                  
    Value* vsize = createIntCst (m_IntPtrTy, size);
    Assert (m_B.CreateICmpSLE (voffset_addr_sz, vsize),
	    bb2, bb1, insertPt, mkBBName ("overflow_error",base));
    
    if (!InstrumentUnderflow)  {
      BranchInst::Create (cont, bb2);
    } else {
      // underflow
      BasicBlock* bb2_then = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
      BasicBlock* bb2_else = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
      BasicBlock* bb3 = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
      m_B.SetInsertPoint (bb2); 
      Value* vtracked_base = createLoad(m_B, m_tracked_base, m_dl);      
      Value* vbase = m_B.CreateBitOrPointerCast (base, geti8PtrTy (ctx));
      BranchInst::Create (bb2_then, bb2_else, 
			  m_B.CreateICmpEQ (vtracked_base, vbase), bb2);            
      
      BasicBlock* abc_under_bb1 = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
      BasicBlock* abc_under_bb2 = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
      BranchInst::Create (abc_under_bb1, bb2_then);      
      // assert (offset >= 0);
      m_B.SetInsertPoint (abc_under_bb1);
      Assert (m_B.CreateICmpSGE (voffset, createIntCst (m_IntPtrTy, 0)), 
	      cont, abc_under_bb1, insertPt, mkBBName("underflow_error",base));
      
      m_B.SetInsertPoint (bb2_else); 
      Value* vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);      
      BranchInst::Create (bb3, cont, 
			  m_B.CreateICmpEQ (vtracked_ptr, vbase), bb2_else);            
      
      m_B.SetInsertPoint (bb3); 
      Value* vtracked_offset = createLoad(m_B, m_tracked_offset, m_dl);      
      BranchInst::Create (abc_under_bb2, bb3);      
      // assert (tracked_offset + offset >= 0);
      m_B.SetInsertPoint (abc_under_bb2);
      Assert (m_B.CreateICmpSGE (createAdd (m_B, m_dl, voffset, vtracked_offset), 
				 createIntCst (m_IntPtrTy, 0)), 
	      cont, abc_under_bb2, insertPt, mkBBName("underflow_error",base));
      
    }
    
    m_gep_known_size_and_offset_checks_added += (!InstrumentUnderflow ? 1 : 2);      
  }
  
  //! Instrument a load/store whose pointer is coming from a Gep and
  //! the object has an unknown size.
  void Global::InstVis::doGepPtrCheck (GetElementPtrInst* gep, 
				       Instruction* insertPt) {
    
    int addr_sz = getAddrSize (m_dl, *insertPt);
    if (addr_sz < 0) { // this should not happen
      report_fatal_error("ABC pass cannot find size of address");
    }
    
    // -- compute offset and insert it just before the gep instruction
    m_B.SetInsertPoint (gep); 
    Value* voffset = computeGepOffset (m_dl, m_B, gep);
    Value* voffset_addr_sz = createAdd (m_B, m_dl, voffset, 
					     createIntCst (m_IntPtrTy, addr_sz),
					     "off.addr_sz");
    
    // -- insertPt is one instruction after the gep instruction
    LLVMContext& ctx = m_B.getContext ();
    BasicBlock* bb = insertPt->getParent ();
    Function* F = bb->getParent ();
    BasicBlock *cont = bb->splitBasicBlock(insertPt);
    m_B.SetInsertPoint (bb->getTerminator ());
    
    Value* base = gep->getPointerOperand ();
    BasicBlock* bb1 = BasicBlock::Create(ctx, mkBBName("check_gep_base_if",base), F);
    BasicBlock* bb1_then = BasicBlock::Create(ctx, mkBBName("check_gep_base_then",base), F);
    BasicBlock* bb1_else = BasicBlock::Create(ctx, mkBBName("check_gep_base_else",base), F);
    BasicBlock* bb2 = BasicBlock::Create(ctx, mkBBName("check_gep_base_ptr",base), F);
    bb->getTerminator ()->eraseFromParent ();      
    BranchInst::Create (bb1, bb);      
    
    /*
      bb1:
      if (base == tracked_base) goto bb1_then else goto bb1_else
	   bb1_then:
           assert (offset >= 0);
           assert (offset + addr_sz <= tracked_size);
           goto cont;
      bb1_else:
           if (base == tracked_ptr) goto bb2 else goto cont
      bb2:
           assume (tracked_ptr > tracked_base);
           assert (tracked_offset + offset >= 0);
           assert (tracked_offset + offset + addr_sz <= tracked_size);
           goto cont;
      cont:
           load or store
    */

    
    m_B.SetInsertPoint (bb1); 
    
    /// --- special step: use llvm machinery to figure out the size
    SizeOffsetEvalType Data = m_eval.compute (base);
    Value* size = Data.first;
    bool IsKnownSize;
    if (size) {
      size =  m_B.CreateZExtOrTrunc (size, 
				     createIntTy (m_dl, m_B.getContext ()));
      IsKnownSize=true;
    } else {
      size = createLoad(m_B, m_tracked_size, m_dl);      
      IsKnownSize=false;
    }
    
    Value* vtracked_base = createLoad(m_B, m_tracked_base, m_dl);      
    Value* vbase = m_B.CreateBitOrPointerCast (base, geti8PtrTy (ctx));
    BranchInst::Create (bb1_then, bb1_else, 
			m_B.CreateICmpEQ (vtracked_base, vbase), bb1);            
    
    BasicBlock* abc_under_bb1 = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
    BasicBlock* abc_over_bb1 = BasicBlock::Create(ctx, mkBBName("over_check",base), F);
    BranchInst::Create (abc_under_bb1, bb1_then);      
    
    // assert (offset >= 0);
    
    if (!InstrumentUnderflow)  {
      BranchInst::Create (abc_over_bb1, abc_under_bb1);
    } else {
      m_B.SetInsertPoint (abc_under_bb1);
      Assert (m_B.CreateICmpSGE (voffset, createIntCst (m_IntPtrTy, 0)), 
	      abc_over_bb1, abc_under_bb1, insertPt, mkBBName("underflow_error",base));
    }
    
    // assert (offset + addr_sz <= tracked_size);
    m_B.SetInsertPoint (abc_over_bb1);
    Assert (m_B.CreateICmpSLE (voffset_addr_sz, size), 
	    cont, abc_over_bb1, insertPt, mkBBName("overflow_error",base));
    
    if (TrackBaseOnly) {
      BranchInst::Create (cont, bb1_else); 
    } else {
      m_B.SetInsertPoint (bb1_else); 
      Value* vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);      
      BranchInst::Create (bb2, cont, 
			  m_B.CreateICmpEQ (vtracked_ptr, vbase), bb1_else);            
      
      m_B.SetInsertPoint (bb2); 
      // assume (tracked_ptr > tracked_base);
      Assume (m_B.CreateICmpSGT (vtracked_ptr, vtracked_base), F);
      
      Value* vtracked_offset = createLoad(m_B, m_tracked_offset, m_dl);      
      BasicBlock* abc_under_bb2 = BasicBlock::Create(ctx, mkBBName("under_check",base), F);
      BasicBlock* abc_over_bb2 = BasicBlock::Create(ctx, mkBBName("over_check",base), F);
      BranchInst::Create (abc_under_bb2, bb2); 
      
      // assert (tracked_offset + offset >= 0);
      if (!InstrumentUnderflow)  {
	BranchInst::Create(abc_over_bb2, abc_under_bb2);
      } else {
	m_B.SetInsertPoint (abc_under_bb2);
	Assert (m_B.CreateICmpSGE (createAdd (m_B, m_dl, voffset, vtracked_offset), 
				   createIntCst (m_IntPtrTy, 0)), 
		abc_over_bb2, abc_under_bb2, insertPt, mkBBName("underflow_error",base));
      }
      
      // assert (tracked_offset + offset + addr_sz <= tracked_size);
      m_B.SetInsertPoint (abc_over_bb2);
      Assert (m_B.CreateICmpSLE(createAdd(m_B,m_dl,vtracked_offset,voffset_addr_sz),size),
	      cont, abc_over_bb2, insertPt, mkBBName("overflow_error",base));
    }
    
    if (IsKnownSize)
      m_gep_known_size_checks_added += (!InstrumentUnderflow ? 1 : 2);        
    else
        m_gep_unknown_size_checks_added += (!InstrumentUnderflow ? 1 : 2);        
  }
  
  //! Instrument any read or write to a pointer that is not coming
  //! from a gep (e.g., from other load instructions and formal
  //! parameters).
  void Global::InstVis::doPtrCheck (Value* Ptr, Value* N /*bytes*/, 
                                    Instruction* insertPt) {
    
    /*  
	if N is null then the check corresponds to a store/load
	The added code is:

        if (tracked_ptr && p == tracked_ptr) {
           assert (tracked_offset + addr_size <= tracked_size);
           assert (tracked_offset >= 0);
        }

        TODO: we should also split if p == tracked_base

        otherwise, the check corresponds to a memory intrinsic
        (memcpy, memmove, or memset). The code differs slightly:

        if (tracked_ptr && p == tracked_ptr) {
            assert (tracked_offset + n <= tracked_size);
            assert (tracked_offset >= 0);
        }
    */
    
    LLVMContext& ctx = m_B.getContext ();
    BasicBlock* bb = insertPt->getParent ();
    Function* F = bb->getParent ();
    
    BasicBlock* abc_under_bb = BasicBlock::Create(ctx, mkBBName("under_check",Ptr), F);
    BasicBlock* abc_over_bb = BasicBlock::Create(ctx, mkBBName("over_check",Ptr), F);
    
    
    BasicBlock *cont = bb->splitBasicBlock(insertPt);
    m_B.SetInsertPoint (bb->getTerminator ());
    
    // if (m_tracked_ptr && ptr == m_tracked_ptr)
    Value* vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);
    Value* condA = m_B.CreateICmpSGT(vtracked_ptr, 
				     createNullCst (ctx));
    Value* condB = m_B.CreateICmpEQ (vtracked_ptr,
				     m_B.CreateBitOrPointerCast (Ptr, geti8PtrTy (ctx)));
    Value* cond = m_B.CreateAnd (condA, condB);
    bb->getTerminator ()->eraseFromParent ();      
    BranchInst::Create (abc_under_bb, cont, cond, bb);      
    m_B.SetInsertPoint (abc_under_bb);
    
    Value* offset = createLoad(m_B, m_tracked_offset, m_dl);
    
    // --- special step: use llvm machinery to figure out the size
    SizeOffsetEvalType Data = m_eval.compute (Ptr);
    Value* Size = Data.first;
    bool IsKnownSize;
    if (Size) {
      Size =  m_B.CreateZExtOrTrunc (Size, createIntTy (m_dl, m_B.getContext()));
      IsKnownSize=true;
    } else {
      Size = createLoad(m_B, m_tracked_size, m_dl);      
      IsKnownSize=false;
    }
    
    /////
    // underflow check
    /////
    
    if (!InstrumentUnderflow)  {
      BranchInst::Create (abc_over_bb, abc_under_bb);
    } else {
      // abc_under_bb:
      //    if (m_tracked_offset >= 0) goto abc_over_bb else goto err_under_bb
      
      Assert (m_B.CreateICmpSGE (offset, createIntCst (m_IntPtrTy, 0)), 
	      abc_over_bb, abc_under_bb, insertPt, mkBBName("underflow_error",Ptr));
    }
    
    /////
    // overflow check
    /////
    
    m_B.SetInsertPoint (abc_over_bb);
    
    // abc_over_bb:
    // We have two cases whether n is not null or not.
    // 
    // case a)
    //    if (m_tracked_offset + n <= m_tracked_size) 
    //        goto cont 
    //    else 
    //        goto err_over_bb
    // case b)
    //    if (m_tracked_offset + addr_size <= m_tracked_size) 
    //        goto cont 
    //    else 
    //        goto err_over_bb
    if (N) {
      // both offset and N are in bytes
      offset = createAdd (m_B, m_dl, offset, N);
    } else {
      int addr_sz = getAddrSize (m_dl, *insertPt);
      if (addr_sz < 0) { // this should not happen
	report_fatal_error("ABC pass cannot find size of address");
      }
      // both offset and addr_sz are in bytes
      offset = createAdd (m_B, m_dl, 
			       offset, 
			       createIntCst (m_IntPtrTy, addr_sz));
    }
    
    Assert (m_B.CreateICmpSLE (offset, Size), cont, abc_over_bb, 
	    insertPt, mkBBName("overflow_error",Ptr));                
    
    if (IsKnownSize)
      m_non_gep_known_size_checks_added += (!InstrumentUnderflow ? 1 : 2);        
    else
      m_non_gep_unknown_size_checks_added += (!InstrumentUnderflow ? 1 : 2);        
  }

  Global::InstVis::InstVis (Module& M, 
                            const DataLayout* dl, 
                            const TargetLibraryInfo* tli,
                            IRBuilder<> B, CallGraph* cg,
                            DsaWrapper *dsa,
                            Function* errorFn, Function* assumeFn): 
    m_dl (dl), m_tli (tli), 
    m_B (B), m_cg (cg), m_dsa (dsa),
    m_eval (dl, tli, B.getContext (), true),             
    m_IntPtrTy (dl->getIntPtrType (M.getContext (), 0)),
    m_nondet_id (0),
    m_tracked_base (nullptr), m_tracked_ptr (nullptr),
    m_tracked_offset (nullptr), m_tracked_size (nullptr), 
    m_tracked_escaped_ptr (nullptr),
    m_errorFn (errorFn), m_assumeFn (assumeFn),
    m_checks_added (0), m_trivial_checks (0),
    m_untracked_dsa_checks (0), m_mem_accesses (0), 
    m_intrinsics_checks_added (0),
    m_gep_known_size_and_offset_checks_added (0),
    m_gep_known_size_checks_added (0),
    m_gep_unknown_size_checks_added (0),
    m_non_gep_known_size_checks_added (0),
    m_non_gep_unknown_size_checks_added (0) { doInit (M);}    
  
  void Global::InstVis::visit (GetElementPtrInst *I) {
    if (!IsTrivialCheck (m_dl, m_tli, dyn_cast<Value> (I))) {
      // This point is reached only if canEscape returned true
      doPtrArith (I, getNextInst (I));
    }
  }
  
  void Global::InstVis::visit (LoadInst *I) {
    Value* ptr = I->getPointerOperand ();
    if (globalGeneratedBySeaHorn (ptr)) return;
    
    Function &F = *(I->getParent()->getParent());      
    if (m_dsa->shouldBeTrackedPtr (*ptr, F, __LINE__)) {      
      m_mem_accesses++;
      if (IsTrivialCheck (m_dl, m_tli, ptr)) {
	m_trivial_checks++;
	return;
      }
      
      // XXX: probably better if we strip pointer casts
      // ptr = ptr->stripPointerCasts ();
      
      if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst> (ptr)) {
	uint64_t size; //bytes
	if (seahorn::getObjectSize(gep->getPointerOperand (), size, m_dl, m_tli, true)) {
	  doGepOffsetCheck (gep, size, I);
	} else  {
	  doGepPtrCheck (gep, I);
	}
      } else {
	doPtrCheck (ptr, nullptr, I);
      }
      m_checks_added += (!InstrumentUnderflow?1:2);
      
    } else {
      m_untracked_dsa_checks ++;	
    }
    
    if (StoreBaseOnly) {
      if (I->getType()->isPointerTy ()) {
	// Insert "assume ( (lhs >= sea_base && lhs < sea_base + sea_size) => lhs == base)"
	// after the load instruction
	m_B.SetInsertPoint (getNextInst (I));
	LLVMContext& ctx = m_B.getContext ();	  
	
	Value* vtracked_base = createLoad(m_B, m_tracked_base, m_dl);
	Value* vtracked_size = createLoad(m_B, m_tracked_size, m_dl);
	Value* lhs = m_B.CreateBitOrPointerCast (I, geti8PtrTy (ctx));
	
	// negate (lhs >= sea_base && lhs < sea_base + sea_size)
	auto condA = m_B.CreateICmpSLT (lhs, vtracked_base);
	
	// it tricks the alias analysis so tracked_base is not marked as
	// an array:
	//  tmp = nd_ptr ();
	//  assume (tmp == base);
	//  assume (lhs >= tmp + size);
	// auto condB = m_B.CreateICmpSGE (lhs, m_B.CreateGEP(vtracked_base, vtracked_size));
	Function* F = I->getParent()->getParent();
	CallInst* nd_ptr = NonDetPtr (F);
	Assume (m_B.CreateICmpEQ(nd_ptr, vtracked_base), F);
	auto condB = m_B.CreateICmpSGE(lhs, m_B.CreateGEP(nd_ptr, vtracked_size));
	
	// negate (lhs >= sea_base && lhs < sea_base + sea_size) or lhs = base
	Value* cond = m_B.CreateOr (m_B.CreateOr (condA, condB),
				      m_B.CreateICmpEQ (lhs, vtracked_base));
	// insert the assumption
	Assume (cond, I->getParent ()->getParent ());
      }
    }
    
  }
  
  void Global::InstVis::visit (StoreInst *I) {
    Value* ptr = I->getPointerOperand ();      
    if (globalGeneratedBySeaHorn (ptr)) return;
    
    Function &F = *(I->getParent()->getParent());      
    if (m_dsa->shouldBeTrackedPtr (*ptr, F, __LINE__)) {
      m_mem_accesses++;
      if (IsTrivialCheck (m_dl, m_tli, ptr)) {
	m_trivial_checks++;
	return;
      }
      
      if (EscapePtr) {
	// record that the pointer being stored escapes
	if (I->getValueOperand()->getType()->isPointerTy () &&
	    !isa<ConstantPointerNull>(I->getValueOperand())) {
	  /// if (stored value == tracked_ptr) 
	  ///     tracked_escaped_ptr = true
	  LLVMContext& ctx = m_B.getContext ();
	  BasicBlock* bb = I->getParent ();
	  Function* F = bb->getParent ();
	  BasicBlock* cont = bb->splitBasicBlock(getNextInst (I));
	  m_B.SetInsertPoint (bb->getTerminator ());
	  Value* vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);
	  Value* val = m_B.CreateBitOrPointerCast (I->getValueOperand(), 
						   geti8PtrTy (ctx));
	  Value* cond = m_B.CreateICmpEQ (vtracked_ptr, val);
	  bb->getTerminator ()->eraseFromParent ();      
	  BasicBlock* bb1 = BasicBlock::Create(ctx, mkBBName("escaped_ptr",I), F);
	  BranchInst::Create (bb1, cont, cond, bb);    
	  m_B.SetInsertPoint (bb1);
	  createStore(m_B, ConstantInt::getTrue(ctx), m_tracked_escaped_ptr, m_dl);
	  BranchInst::Create (cont, bb1);    
	}
      }
      
      if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst> (ptr)) {
	uint64_t size; // bytes
	if (seahorn::getObjectSize(gep->getPointerOperand (), size, m_dl, m_tli, true))
	  doGepOffsetCheck (gep, size, I);
	else 
	  doGepPtrCheck (gep, I);
      } else 
	doPtrCheck (ptr, nullptr, I);
      
      m_checks_added += (!InstrumentUnderflow?1:2);
      
    } else {
      m_untracked_dsa_checks ++;	
    }
    
    if (StoreBaseOnly) {
      if (I->getValueOperand ()->getType()->isPointerTy ()) {
	// Insert "assert ( (val >= sea_base && val < sea_base + sea_size) => val == base)"
	// after the store instruction
	m_B.SetInsertPoint (getNextInst (I));
	LLVMContext& ctx = m_B.getContext ();	  
	
	Value* vtracked_base = createLoad(m_B, m_tracked_base, m_dl);
	Value* vtracked_size = createLoad(m_B, m_tracked_size, m_dl);
	Value* val = m_B.CreateBitOrPointerCast(I->getValueOperand (),
						geti8PtrTy (ctx));
	
	// negate (val >= sea_base && val < sea_base + sea_size)
	auto condA = m_B.CreateICmpSLT (val, vtracked_base);
	
	// it tricks the alias analysis so tracked_base is not marked as
	// an array:
	//  tmp = nd_ptr ();
	//  assume (tmp == base);
	//  assume (lhs >= tmp + size);
	// auto condB = m_B.CreateICmpSGE (val, m_B.CreateGEP(vtracked_base, vtracked_size));
	Function* F = I->getParent()->getParent();
	CallInst* nd_ptr = NonDetPtr (F);
	Assume (m_B.CreateICmpEQ(nd_ptr, vtracked_base), F);
	auto condB = m_B.CreateICmpSGE(val, m_B.CreateGEP(nd_ptr, vtracked_size));
	
	// negate (val >= sea_base && val < sea_base + sea_size) or val = base
	Value* cond = m_B.CreateOr (m_B.CreateOr (condA, condB),
				    m_B.CreateICmpEQ (val, vtracked_base));
	// code for inserting assertion
	BasicBlock* cur = I->getParent ();
	BasicBlock* cont = cur->splitBasicBlock(m_B.GetInsertPoint ());
	cur->getTerminator()->eraseFromParent ();	  
	Assert (cond, cont, cur, I, "assert_ptr_eq_base_failed");
      }
    }
  }

  void Global::InstVis::visit (MemTransferInst *MTI) {
    Function*F = MTI->getParent()->getParent ();
    unsigned delta_check = (!InstrumentUnderflow ? 1 : 2);      
    Value* dest = MTI->getDest ();
    
    if (m_dsa->shouldBeTrackedPtr (*dest, *F, __LINE__)) {
      m_mem_accesses++;
      
      if (IsTrivialCheck (m_dl, m_tli, dest)) {
	m_trivial_checks++;
      } else {
	m_checks_added += delta_check;
	m_intrinsics_checks_added+= delta_check;
	doPtrCheck (dest, MTI->getLength (), MTI);
      }
    }
    else {
      m_untracked_dsa_checks++;
    }
    
    Value* src = MTI->getSource ();
    if (m_dsa->shouldBeTrackedPtr (*src, *F, __LINE__)) {
      m_mem_accesses++;
      
      if (IsTrivialCheck (m_dl, m_tli, dest)) {
	m_trivial_checks++;
      } else {
	m_checks_added += delta_check;
	m_intrinsics_checks_added+= delta_check;
	doPtrCheck (src, MTI->getLength (), MTI);
      }
    }
    else {
      m_untracked_dsa_checks++;
    }
    
  }
  
  void Global::InstVis::visit (MemSetInst *MSI) {
    Function*F = MSI->getParent()->getParent ();
    unsigned delta_check = (!InstrumentUnderflow ? 1 : 2);
    Value* dest = MSI->getDest ();
    
    if (m_dsa->shouldBeTrackedPtr (*dest, *F, __LINE__)) {
      m_mem_accesses++;
      
      if (IsTrivialCheck (m_dl, m_tli, dest)) {
	m_trivial_checks++;
      } else {
	m_checks_added += delta_check; 
	m_intrinsics_checks_added += delta_check;
	doPtrCheck (dest, MSI->getLength (), MSI);
      }
    }
    else {
      m_untracked_dsa_checks++;
    } 
  }

    // // Check if all alloca's uses are known to be safe
    // bool AllAllocUsesAreTrivial (AllocaInst *AI, 
    //                              std::set<Value*>& TrivialUses) {
     
    //   std::set<Value*> TrivialUsesSoFar;
    //   for (Use& U: AI->uses ()) {
    //     User* UU = U.getUser ();
    //     if (LoadInst* LI = dyn_cast<LoadInst>(UU)) {
    //       if (!IsTrivialCheck (m_dl, m_tli, LI->getPointerOperand ())) 
    //         return false;
    //       else
    //         TrivialUsesSoFar.insert (LI->getPointerOperand ());
    //     } else if (StoreInst* SI = dyn_cast<StoreInst>(UU)) {
    //       if (!IsTrivialCheck (m_dl, m_tli, SI->getPointerOperand ()))
    //         return false;
    //       else
    //         TrivialUsesSoFar.insert (SI->getPointerOperand ());
    //     } else if (GetElementPtrInst * GEP = dyn_cast<GetElementPtrInst> (UU)) {
    //       if (!IsTrivialCheck (m_dl, m_tli, GEP->getPointerOperand ()))
    //         return false;
    //       else 
    //         TrivialUsesSoFar.insert (GEP->getPointerOperand ());
    //     } else {
    //       // XXX: can we do something if the user is a call and we have
    //       // the dereferenceable attribute ? This is very common in C++
    //       // code.
    //       return false;
    //     }
    //   }
    //   TrivialUses.insert (TrivialUsesSoFar.begin(), TrivialUsesSoFar.end ());
    //   return true;
    // }


  // --- Instrument allocation sites
  
  void Global::InstVis::visit (IntToPtrInst *I) {
    doAllocaSite (I, nullptr, getNextInst (I));	      
  }
  
  void Global::InstVis::visit (InsertValueInst *I) {
    // TODO
    if (m_dsa->getAllocSiteId (*I)  == TrackedAllocSite)      
      errs () << "WARNING ABC: missing allocation site from " << *I << "\n";      
    
  }
  
  void Global::InstVis::visit (ExtractValueInst *I) {
    // TODO
    if (m_dsa->getAllocSiteId (*I)  == TrackedAllocSite)      
      errs () << "WARNING ABC: missing allocation site from " << *I << "\n";      
  }  
  
  void Global::InstVis::visit (AllocaInst *I) {
    SizeOffsetEvalType Data = m_eval.compute (I);
    doAllocaSite (I, Data.first ? Data.first : nullptr, getNextInst (I));
  }
  
  void Global::InstVis::visit (CallInst *I) {
    // new, malloc, calloc, realloc, and strdup.
    if (isAllocationFn (I, m_tli, true)) { 
      SizeOffsetEvalType Data = m_eval.compute (I);
      doAllocaSite (I, Data.first ? Data.first : nullptr, getNextInst (I));	
      return;
    }
    
    // External calls are also considered allocation sites
    CallSite CS = CallSite (I);
    if (const Function *callee = CS.getCalledFunction ()) {
      if (callee->isDeclaration ()) {
	Type * retTy = callee->getFunctionType ()->getReturnType ();
	if (retTy->isPointerTy () && isInterestingType(retTy))
	  doAllocaSite (I, nullptr, getNextInst (I));
      }
    } else {
      errs () << "WARNING ABC: run devirt-functions to eliminate all indirect calls "
	      << *I << "\n";
    }
    
    if (DerefAssumptions) {
      // Add extra assumption about the size of the returned value of
      // the call.
      Function* F = I->getParent()->getParent();
      
      if (!(m_dsa->shouldBeTrackedPtr (*I->getArgOperand (0), *F, __LINE__)))
	return;
      
      uint64_t n = I->getDereferenceableBytes (0);
      if (n == 0) return;
      
      m_B.SetInsertPoint (getNextInst (I));
      
      Value* vtracked_base = createLoad(m_B, m_tracked_base, m_dl);
      Value* vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);
      Value* vtracked_size= createLoad(m_B, m_tracked_size, m_dl);
      Value* vtracked_offset= createLoad(m_B, m_tracked_offset, m_dl);
      
      Value* lhs = m_B.CreateBitOrPointerCast (I->getArgOperand (0), 
					       geti8PtrTy (m_B.getContext()));
      Value* N = createIntCst (createIntTy (m_dl, m_B.getContext ()), n);
      
      // assume (lhs == tracked_base -> tracked_size >= n);
      Assume (m_B.CreateOr (m_B.CreateICmpNE (lhs, vtracked_base),
			    m_B.CreateICmpSGE (vtracked_size, N), 
			    "deref_assume"),  F);
      
      // assume (lhs == tracked_ptr -> tracked_size + tracked_offset >= n);
      Assume (m_B.CreateOr (m_B.CreateICmpNE (lhs, vtracked_ptr),
			    m_B.CreateICmpSGE (createAdd (m_B, m_dl, 
							       vtracked_size, vtracked_offset),
					       N), "deref_assume"), F);
    }
  }
  
  void Global::InstVis::visit (Function* F) {
    
    Value *saved_tracked_ptr = nullptr;
    Value *saved_tracked_offset = nullptr;
    if (EscapePtr) {
      if (F->getName () != "main" && !F->empty ()) {
	// Save tracked_ptr and tracked_offset before the function is
	// executed:
	//    saved_tracked_ptr = tracked_ptr
	//    saved_tracked_offset = tracked_offset
	
	if (getReturnInst (F)) {
	  m_B.SetInsertPoint (F->getEntryBlock ().getFirstInsertionPt ());
	  saved_tracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl,
					      "saved_tracked_ptr");
	  saved_tracked_offset = createLoad(m_B, m_tracked_offset, m_dl,
						 "saved_tracked_offset");      
	}
      }
    }
    
    if (DerefAssumptions) {
      // Add extra assumptions about the sizes of the formal paramters
      if (!F->empty () && F->args().begin () != F->args().end ()) {
	
	m_B.SetInsertPoint (F->getEntryBlock ().getFirstInsertionPt ());
        
	Value *vtracked_base, *vtracked_ptr, *vtracked_size, *vtracked_offset;
	vtracked_base = vtracked_ptr = vtracked_size = vtracked_offset = nullptr;
	for (Argument& A : F->args()) {
	  
	  if (!(m_dsa->shouldBeTrackedPtr (A, *F, __LINE__))) continue;
	  uint64_t n = A.getDereferenceableBytes ();
	  if (n == 0) continue;
	  
	  if (!vtracked_base)
	    vtracked_base = createLoad(m_B, m_tracked_base, m_dl);
	  if (!vtracked_ptr)
	    vtracked_ptr = createLoad(m_B, m_tracked_ptr, m_dl);
	  if (!vtracked_size)
	    vtracked_size= createLoad(m_B, m_tracked_size, m_dl);
	  if (!vtracked_offset)
	    vtracked_offset= createLoad(m_B, m_tracked_offset, m_dl);
	  
	  Value* vA = m_B.CreateBitOrPointerCast (&A, geti8PtrTy (m_B.getContext()));
	  Value* N = createIntCst (createIntTy (m_dl, m_B.getContext ()), n);
          
	  // assume (arg == tracked_base -> tracked_size >= n);
	  Assume (m_B.CreateOr (m_B.CreateICmpNE (vA, vtracked_base),
				m_B.CreateICmpSGE (vtracked_size, N), 
				"deref_assume"),  F);
	  
	  // assume (arg == tracked_ptr -> tracked_size + tracked_offset >= n);
	  Assume (m_B.CreateOr (m_B.CreateICmpNE (vA, vtracked_ptr),
				m_B.CreateICmpSGE (createAdd (m_B, m_dl, 
								   vtracked_size, 
								   vtracked_offset),
						   N), "deref_assume"), F);
	}
      }
    }
    
    if (EscapePtr && saved_tracked_ptr) {
      if (ReturnInst* RI = getReturnInst (F)) {
	// restore tracked_ptr if tracked_ptr did not escape:
	//    if (!escaped_ptr)
	//       tracked_ptr = saved_tracked_ptr
	//       tracked_offset = saved_tracked_offset
	LLVMContext& ctx = m_B.getContext ();
	BasicBlock* bb = RI->getParent ();
	BasicBlock* cont = bb->splitBasicBlock(RI);
	m_B.SetInsertPoint (bb->getTerminator ());
	Value *vescaped_ptr = createLoad(m_B, m_tracked_escaped_ptr, m_dl);                
	Value* cond = m_B.CreateICmpEQ (vescaped_ptr, ConstantInt::getFalse (ctx));
	bb->getTerminator ()->eraseFromParent ();      
	BasicBlock* bb1 = BasicBlock::Create(ctx, "restore_tracked_bb", F);
	BranchInst::Create (bb1, cont, cond, bb);    
	m_B.SetInsertPoint (bb1);
	createStore (m_B, saved_tracked_ptr, m_tracked_ptr, m_dl);                
	createStore (m_B, saved_tracked_offset, m_tracked_offset, m_dl);                
	BranchInst::Create (cont, bb1);
      }
    }
  }
  
  bool Global::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
    
    Function* main = M.getFunction ("main");
    if (!main) {
      errs () << "Main not found: no buffer overflow checks added\n";
      return false;
    }
    
    std::unique_ptr<DsaWrapper> dsa (new SeaDsa (this));
    if (!UseSeaDsa)
      dsa.reset (new LlvmDsa (this));
    
    errs () << " --- Using " << dsa->getDsaName () << "\n";
    
    if (TrackedAllocSite > 0)
      {
	if (const Value* allocVal = dsa->getAllocValue (TrackedAllocSite))
	  errs () << "     Allocation site id=" << TrackedAllocSite << "  "
		  << *allocVal << "\n";
      }
    
    LLVMContext &ctx = M.getContext ();
    
    const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfo>();
    const DataLayout * dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
    
    AttrBuilder AB;
    AB.addAttribute (Attribute::NoReturn);
    AttributeSet as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB);
    Function* errorFn = dyn_cast<Function>
      (M.getOrInsertFunction ("verifier.error",
			      as,
			      Type::getVoidTy (ctx), NULL));
    
    AB.clear ();
    as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB); 
    Function* assumeFn = dyn_cast<Function>
      (M.getOrInsertFunction ("verifier.assume", 
			      as,
			      Type::getVoidTy (ctx),
			      Type::getInt1Ty (ctx),
			      NULL));
    
    // Type *intPtrTy = dl->getIntPtrType (ctx, 0);
    // //errs () << "intPtrTy is " << *intPtrTy << "\n";
    // Type *i8PtrTy = Type::getInt8Ty (ctx)->getPointerTo ();
    
    IRBuilder<> B (ctx);
    
    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
    if (cg) {
      cg->getOrInsertFunction (assumeFn);
      cg->getOrInsertFunction (errorFn);
    }
    
    //unsigned untracked_dsa_checks = 0;
    SmallVector<Instruction*, 16> ToInstrument;
    // We instrument every address only once per basic block
    SmallSet<Value*, 16> TempsToInstrument;
    bool IsWrite;
    unsigned Aligment;
    
    for (Function &F : M) {
      
      if (F.isDeclaration ()) continue;
      
      // -- skip special functions
      if (F.getName ().startswith ("seahorn.") ||
	  F.getName ().startswith ("shadow.") ||
	  F.getName ().startswith ("verifier.")) continue;
      
      for (auto &BB : F) {
	TempsToInstrument.clear();
        
	for (auto &i: BB)  {
	  Instruction *I = &i;
	  
	  //////
	  // Instructions that should be instrumented
	  //////
	  if (GetElementPtrInst* GEP  = dyn_cast<GetElementPtrInst> (I)) {
	    Value *ptr = GEP->getPointerOperand ();            
	    if (isInterestingType (ptr->getType()) && 
		dsa->shouldBeTrackedPtr (*ptr, F, __LINE__) && 
		canEscape (GEP)) {
	      ToInstrument.push_back (I);
	    }
	  } // load/store instructions
	  else if (Value *Addr = isInterestingMemoryAccess(I, &IsWrite, &Aligment)) {
	    // We've seen this temp in the current BB.
	    if (!TempsToInstrument.insert(Addr).second) continue;  
	    //if (dsa->shouldBeTrackedPtr (*Addr, F, __LINE__)) {
	    ToInstrument.push_back (I);
	    //}
	    //else
	    //  untracked_dsa_checks++; 
	  }
	  else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
	    if (!InstrumentMemIntrinsics) continue;
	    // if (dsa->shouldBeTrackedPtr (*MTI->getDest (), F, __LINE__) || 
	    //    dsa->shouldBeTrackedPtr (*MTI->getSource (),F, __LINE__))
	    ToInstrument.push_back (I);
	    //else 
	    //untracked_dsa_checks+=2; 
	  }
	  else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
	    if (!InstrumentMemIntrinsics) continue;
	    //if (dsa->shouldBeTrackedPtr (*MSI->getDest (), F, __LINE__)) 
	    ToInstrument.push_back (I);
	    //else 
	    //untracked_dsa_checks++; 
	  }
	  ///////
	  // Instructions that can return allocation sites
	  ///////
	  else if (AllocaInst* AI = dyn_cast<AllocaInst>(I)) {
	    /// XXX: isInterestingAlloca returns false if the size
	    /// is not statically known so we would miss some cases
	    if (/*isInterestingType (I->getType ())*/
		isInterestingAlloca (dl, *AI) && 
		dsa->shouldBeTrackedPtr (*I, F, __LINE__))
	      ToInstrument.push_back (I);		
	  }
	  else if (isa<IntToPtrInst> (I)) {
	    if (isInterestingType (I->getType ()) &&
		dsa->shouldBeTrackedPtr (*I, F, __LINE__))
	      ToInstrument.push_back (I);		
	  }
	  else if (isa<InsertValueInst> (I)) {
	    //if (dsa->shouldBeTrackedPtr (*I, F, __LINE__))
	    ToInstrument.push_back (I);		
	  }
	  else if (isa<ExtractValueInst> (I)) {
	    //if (dsa->shouldBeTrackedPtr (*I, F, __LINE__))
	    ToInstrument.push_back (I);		
	  }
	  else if (isa<CallInst> (I)){
	    if (dsa->shouldBeTrackedPtr (*I, F, __LINE__))
	      ToInstrument.push_back (I);
	  }
	}
      }
    }
    
    InstVis abc (M, dl, tli, B, cg, &*dsa, errorFn, assumeFn);

    for (Function &F : M) {
      if (F.isDeclaration ()) continue;
      abc.visit (&F);
    }
    
    // process the worklist
    for (auto I: ToInstrument) {
      if (GetElementPtrInst * GEP  = dyn_cast<GetElementPtrInst> (I)) {
	abc.visit (GEP);
      } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
	abc.visit (LI);		  
      } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
	abc.visit (SI);	  
      } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
	abc.visit (MTI);        
      } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
	abc.visit (MSI);        
      } else if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
	abc.visit (AI);
      } else if (IntToPtrInst *IToPI = dyn_cast<IntToPtrInst>(I)) {
	abc.visit (IToPI);
      } else if (InsertValueInst *IVI = dyn_cast<InsertValueInst>(I)) {
	abc.visit (IVI);
      } else if (ExtractValueInst *EVI = dyn_cast<ExtractValueInst>(I)) {
	abc.visit (EVI);
      } else if (CallInst *CI = dyn_cast<CallInst>(I)) {
	abc.visit (CI);
      }
    }
    
    errs () << " ========== ABC  ==========\n";
    if (TrackedAllocSite > 0)
      errs ()<< " ## Soundness note: accesses within Dsa nodes without an allocation site are not instrumented.\n\n";
    
    errs () << "-- " << abc.m_trivial_checks
	    << " Total number of trivially safe memory reads/writes (not instrumented)\n"
	    << "-- " << abc.m_mem_accesses - abc.m_trivial_checks
	    << " Total number of non-trivial memory reads/writes\n"
	    << "-- " << abc.m_checks_added
	    << " Total number of added checks\n"
	    << "      " << abc.m_checks_added - abc.m_intrinsics_checks_added
	    << " Total number of added checks for load and store\n"
	    << "      " << abc.m_intrinsics_checks_added
	    << " Total number of added checks for memory intrinsics\n"
	    << "          " << abc.m_gep_known_size_and_offset_checks_added
	    << " Total number of added checks for gep pointers with known size and offset\n"
	    << "          " << abc.m_gep_known_size_checks_added
	    << " Total number of added checks for gep pointers with known size\n"
	    << "          " << abc.m_gep_unknown_size_checks_added
	    << " Total number of added checks for gep pointers with unknown size\n"
	    << "          " << abc.m_non_gep_known_size_checks_added
	    << " Total number of added checks for non-gep pointers with known size\n"
	    << "          " << abc.m_non_gep_unknown_size_checks_added
	    << " Total number of added checks for non-gep pointers with unknown size\n";
    
    if (TrackedDsaNode != 0) {
      errs () << "-- " << abc.m_untracked_dsa_checks 
	      << " Total number of skipped checks because untracked Dsa node\n";
    }
    //errs () << M << "\n";
    return true;
  }
  
  void Global::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<seahorn::DSAInfo>();     // run llvm dsa
    AU.addRequired<sea_dsa::DsaInfoPass>(); // run seahorn dsa
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::TargetLibraryInfo>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addRequired<llvm::CallGraphWrapperPass>(); 
    // for debugging
    //AU.addRequired<ufo::NameValues> ();
  } 
  
  char Global::ID = 0;
  
  static llvm::RegisterPass<Global> 
  Y ("abc-global", "Insert array buffer checks using Global encoding");

  
  bool GlobalCCallbacks::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
    
    Function* main = M.getFunction ("main");
    if (!main) {
      errs () << "Main not found: no buffer overflow checks added\n";
      return false;
    }
    
    const TargetLibraryInfo * tli = &getAnalysis<TargetLibraryInfo>();
    const DataLayout* dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
    
    std::unique_ptr<DsaWrapper> dsa (new SeaDsa (this));
    if (!UseSeaDsa)
      dsa.reset (new LlvmDsa (this));
    
    errs () << " Using " << dsa->getDsaName () << "\n\n";
    
    LLVMContext &ctx = M.getContext ();
    Type *voidTy = Type::getVoidTy (ctx);
    Type *intPtrTy = dl->getIntPtrType (ctx, 0);
    //errs () << "intPtrTy is " << *intPtrTy << "\n";
    Type *i8PtrTy = Type::getInt8Ty (ctx)->getPointerTo ();
    
    AttrBuilder AB;
    AttributeSet as = AttributeSet::get (ctx, AttributeSet::FunctionIndex, AB); 
    
    Function* abc_init = dyn_cast<Function>
      (M.getOrInsertFunction ("sea_abc_init",
			      as, voidTy, NULL));
    abc_init->addFnAttr(Attribute::AlwaysInline);
    
    Function* abc_alloc = dyn_cast<Function>
      (M.getOrInsertFunction ("sea_abc_alloc",
			      as, voidTy, i8PtrTy, intPtrTy,
			      NULL));
    abc_alloc->addFnAttr(Attribute::AlwaysInline);
    
    Function* abc_log_ptr = dyn_cast<Function>
      (M.getOrInsertFunction ("sea_abc_log_ptr",
			      as, voidTy, i8PtrTy, intPtrTy,
			      NULL));
    abc_log_ptr->addFnAttr(Attribute::AlwaysInline);
    
    Function* abc_log_load_ptr = dyn_cast<Function>
      (M.getOrInsertFunction ("sea_abc_log_load_ptr",
			      as, voidTy, i8PtrTy, i8PtrTy,
			      NULL));
    abc_log_load_ptr->addFnAttr(Attribute::AlwaysInline);
    
    Function* abc_log_store_ptr = dyn_cast<Function>
      (M.getOrInsertFunction ("sea_abc_log_store_ptr",
			      as, voidTy, i8PtrTy, i8PtrTy,
			      NULL));
    abc_log_store_ptr->addFnAttr(Attribute::AlwaysInline);
    
    Function* abc_assert_valid_ptr = dyn_cast<Function>
      (M.getOrInsertFunction ("sea_abc_assert_valid_ptr",
			      as, voidTy, i8PtrTy, intPtrTy,
			      NULL));
    abc_assert_valid_ptr->addFnAttr(Attribute::AlwaysInline);
    
    Function* abc_assert_valid_offset = dyn_cast<Function>
      (M.getOrInsertFunction ("sea_abc_assert_valid_offset",
			      as, voidTy, intPtrTy, intPtrTy,
			      NULL));
    abc_assert_valid_offset->addFnAttr(Attribute::AlwaysInline);
    
    Function* assumeFn = dyn_cast<Function>
      (M.getOrInsertFunction ("verifier.assume", 
			      as,
			      Type::getVoidTy (ctx),
			      Type::getInt1Ty (ctx),
			      NULL));
    
    std::vector<Function*> sea_funcs = 
      { abc_assert_valid_offset, abc_assert_valid_ptr, 
	abc_log_ptr, abc_log_load_ptr, abc_log_store_ptr, abc_alloc, abc_init,
	assumeFn
      };
    
    
    GlobalVariable *LLVMUsed = M.getGlobalVariable("llvm.used");
    std::vector<Constant*> MergedVars;
    if (LLVMUsed) {
      // Collect the existing members of llvm.used except sea
      // functions
      ConstantArray *Inits = cast<ConstantArray>(LLVMUsed->getInitializer());
      for (unsigned I = 0, E = Inits->getNumOperands(); I != E; ++I) {
	Value* V = Inits->getOperand(I)->stripPointerCasts();
	if (std::find (sea_funcs.begin (), sea_funcs.end (),
		       V) == sea_funcs.end ()) {
	  MergedVars.push_back(Inits->getOperand(I));
	}
      }
      LLVMUsed->eraseFromParent();
    }
    
    // Recreate llvm.used.
    if (!MergedVars.empty ()) {
      ArrayType *ATy = ArrayType::get(geti8PtrTy (ctx), MergedVars.size());
      LLVMUsed = new llvm::GlobalVariable
	(M, ATy, false, llvm::GlobalValue::AppendingLinkage,
	 llvm::ConstantArray::get(ATy, MergedVars), "llvm.used");
      LLVMUsed->setSection("llvm.metadata");
    }
    
    IRBuilder<> B (ctx);
    
    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    CallGraph* cg = cgwp ? &cgwp->getCallGraph () : nullptr;
    if (cg) {
      cg->getOrInsertFunction (abc_init);
      cg->getOrInsertFunction (abc_alloc);
      cg->getOrInsertFunction (abc_log_ptr);
      cg->getOrInsertFunction (abc_log_load_ptr);
      cg->getOrInsertFunction (abc_log_store_ptr);		
      cg->getOrInsertFunction (abc_assert_valid_ptr);
      cg->getOrInsertFunction (abc_assert_valid_offset);
      
      cg->getOrInsertFunction (assumeFn);
    }
    
    unsigned untracked_dsa_checks = 0;
    unsigned checks_added = 0;
    unsigned trivial_checks = 0;
    unsigned mem_accesses = 0;
    DenseMap<GetElementPtrInst*, Value*> instrumented_gep;
    ObjectSizeOffsetEvaluator size_offset_eval (dl, tli, ctx, true);
    
    // do initialization
    B.SetInsertPoint (main->getEntryBlock ().getFirstInsertionPt ());
    updateCallGraph (cg, main, B.CreateCall (abc_init));
    
    // allocation of global variables
    for (auto &GV: M.globals ()) {
      
      Type *Ty = cast<PointerType>(GV.getType())->getElementType();
      if (!Ty->isSized()) continue;
      if (!GV.hasInitializer()) continue;
      if (!(dsa->shouldBeTrackedPtr (GV, *main, __LINE__))) continue;
      if (GV.hasSection()) {
	StringRef Section(GV.getSection());
	// Globals from llvm.metadata aren't emitted, do not instrument them.
	if (Section == "llvm.metadata") continue;
      }
      if (GV.getName ().startswith ("sea_")) continue;
      
      
      uint64_t size;
      if (seahorn::getObjectSize(&GV, size, dl, tli, true)) {
	Value* baseAddr = B.CreateBitOrPointerCast (&GV,geti8PtrTy (ctx));
	Value* allocSize = createIntCst (intPtrTy, size);
	CallInst *CI = B.CreateCall2 (abc_alloc, baseAddr, allocSize);
	//errs () << "*** allocating global " << GV << "\n" << "\t" << *CI << "\n";
	updateCallGraph (cg, main, CI);
      }
      else {// this should not happen unless global is external
	errs () << "WARNING ABC: missing allocation site from global " << GV
		<< " because its size cannot be inferred statically.\n";
      }
    }
    
    // We instrument every address only once per basic block
    SmallSet<Value*, 16> TempsToInstrument;
    bool IsWrite;
    unsigned Aligment;
    
    for (Function &F : M) {
      
      if (F.isDeclaration ()) continue;
      
      // skip sea functions
      if (std::find (sea_funcs.begin (), sea_funcs.end (), &F) != sea_funcs.end ())  
	continue;
      
      // -- skip special functions
      if (F.getName ().startswith ("seahorn.") ||
	  F.getName ().startswith ("shadow.") ||
	  F.getName ().startswith ("verifier.")) continue;
      
      for (auto&BB : F)  {
	
	for (auto &i: BB) {
	  Instruction *I = &i;
	  if (GetElementPtrInst* GEP  = dyn_cast<GetElementPtrInst> (I)) {
	    Value *base = GEP->getPointerOperand ();            
	    if (dsa->shouldBeTrackedPtr (*base, F, __LINE__) && 
		isInterestingType (base->getType()) && 
		canEscape (GEP) && 
		!IsTrivialCheck (dl, tli, dyn_cast<Value> (I))) {
	      
	      B.SetInsertPoint (GEP); 
	      Value* offset = computeGepOffset (dl, B, GEP);                  
	      instrumented_gep [GEP] = offset;
	      Value* base8Ptr = B.CreateBitOrPointerCast (base, geti8PtrTy (ctx));
	      updateCallGraph (cg,&F,B.CreateCall2 (abc_log_ptr, base8Ptr, offset));  
	    }
	  } else if (Value *ptr = isInterestingMemoryAccess(I, &IsWrite, &Aligment)) {
	    // XXX: this may help
	    //ptr = ptr->stripPointerCasts ();
	    
	    // We've seen this temp in the current BB.
	    if (!TempsToInstrument.insert(ptr).second) continue;  
	    
	    if (ptr->getName ().startswith ("sea_")) continue;
	    
	    if (dsa->shouldBeTrackedPtr (*ptr, F, __LINE__)) { 
	      mem_accesses++;
	      if (IsTrivialCheck (dl, tli, ptr)) {
		trivial_checks++;
	      } else {
		int uaddrSz = getAddrSize (dl, *I);
		if (uaddrSz < 0) report_fatal_error("ABC: cannot find size of address");
		Value* addrSz = createIntCst (intPtrTy, uaddrSz);
		
		checks_added++;
		// ptr is a gep
		if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst> (ptr)) {
		  B.SetInsertPoint (gep);
		  Value* offset = instrumented_gep [gep];
		  if (!offset) offset = computeGepOffset (dl, B, gep);
		  // offset adjusted by pointer size		    
		  offset = createAdd (B, dl, offset, addrSz);
		  B.SetInsertPoint (I);
		  Value* base = gep->getPointerOperand ();
		  uint64_t size; //bytes
		  if (seahorn::getObjectSize(base, size, dl, tli, true)) {
		    Value* vsize = createIntCst (intPtrTy, size);
		    CallInst *CI = B.CreateCall2(abc_assert_valid_offset, offset, vsize);
		    updateCallGraph (cg, &F, CI);
		    //errs () << "**** ptr is a gep of known size " << *I << "\n"; 
		    //errs () << "\t" << *CI << "\n";		      
		  }
		  else {
		    base = B.CreateBitOrPointerCast (base, geti8PtrTy (ctx));
		    CallInst *CI = B.CreateCall2 (abc_assert_valid_ptr, base, offset);
		    updateCallGraph(cg, &F, CI);
		    //errs () << "**** ptr is a gep but unknown size " << *I << "\n";
		    //errs () << "\t" << *CI << "\n";
		  }
		}
		// ptr is not a gep
		else { 
		  B.SetInsertPoint (I);
		  Value* base = B.CreateBitOrPointerCast (ptr, geti8PtrTy (ctx));
		  CallInst * CI = B.CreateCall2 (abc_assert_valid_ptr, base, addrSz);
		  updateCallGraph (cg, &F, CI);		    
		  //errs () << "**** ptr is not a gep " << *I << "\n";
		  //errs () << "\t" << *CI << "\n";
		}		  
	      }
	    }
	    else  {
	      untracked_dsa_checks++;
	    }
	    
	    ///////
	    // Add code load and store instructions.
	    // XXX: even if the load/store is not tracked we insert
	    //      these special function calls.
	    //////
	    if (LoadInst *LI = dyn_cast<LoadInst> (I)) {
	      if (LI->getType()->isPointerTy ()) { // a pointer is read from memory
		// insert instrumentation after the load 		  
		B.SetInsertPoint (getNextInst (I)); 
		Value* lhs = B.CreateBitOrPointerCast (I, geti8PtrTy (ctx));
		Value* ptr = B.CreateBitOrPointerCast (LI->getPointerOperand (), geti8PtrTy (ctx));		    
		updateCallGraph (cg, &F, B.CreateCall2 (abc_log_load_ptr, lhs, ptr));
	      }
	    } else if (StoreInst *SI = dyn_cast<StoreInst> (I)) {
	      if (SI->getValueOperand()->getType()->isPointerTy ()) {
		// a pointer is written into memory
		B.SetInsertPoint (I); // insert instrumentation before the store 
		Value* value = B.CreateBitOrPointerCast (SI->getValueOperand (), geti8PtrTy (ctx));
		Value* ptr = B.CreateBitOrPointerCast (SI->getPointerOperand (), geti8PtrTy (ctx));		    
		updateCallGraph (cg, &F, B.CreateCall2 (abc_log_store_ptr, value, ptr));
	      }
	    }
	    
	  } else if (MemTransferInst *MTI = dyn_cast<MemTransferInst>(I)) {
	    if (!InstrumentMemIntrinsics) continue;
            
	    if (dsa->shouldBeTrackedPtr (*MTI->getDest (), F, __LINE__) || 
		dsa->shouldBeTrackedPtr (*MTI->getSource (), F, __LINE__)) {
	      mem_accesses+=2;
	      B.SetInsertPoint (MTI); 
              
	      Value* dest = MTI->getDest ();
	      Value *len = nullptr;
	      if (IsTrivialCheck (dl, tli, dest)) {
		trivial_checks++;
	      } else {
		checks_added++;
		Value *base = B.CreateBitOrPointerCast (dest, geti8PtrTy(ctx));
		len = B.CreateZExtOrTrunc (MTI->getLength(), intPtrTy);
		updateCallGraph (cg, &F, B.CreateCall2 (abc_assert_valid_ptr, base, len));
	      }
              
	      Value* src = MTI->getSource ();
	      if (IsTrivialCheck (dl, tli, src)) {
		trivial_checks++;
	      } else {
		checks_added++; 
		if (!len) len = B.CreateZExtOrTrunc (MTI->getLength(), intPtrTy);
		Value *base = B.CreateBitOrPointerCast (src, geti8PtrTy(ctx));
		updateCallGraph (cg, &F, B.CreateCall2 (abc_assert_valid_ptr, base, len));
	      }
	    }
	    else 
	      untracked_dsa_checks+=2; 
	  } else if (MemSetInst *MSI = dyn_cast<MemSetInst>(I)) {
	    if (!InstrumentMemIntrinsics) continue;
            
	    Value* ptr = MSI->getDest ();
	    if (dsa->shouldBeTrackedPtr (*ptr, F, __LINE__))  {
	      mem_accesses++;
	      Value* dest = MSI->getDest ();
	      B.SetInsertPoint (MSI); 
	      if (IsTrivialCheck (dl, tli, dest)) {
		trivial_checks++;
	      } else {
		checks_added++; 
		Value *base = B.CreateBitOrPointerCast (dest, geti8PtrTy(ctx));
		Value *len = B.CreateZExtOrTrunc (MSI->getLength(), intPtrTy);
		updateCallGraph (cg, &F, B.CreateCall2 (abc_assert_valid_ptr, base, len));
	      }
	    }
	    else 
	      untracked_dsa_checks++; 
	  } else if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) {
	    if (!isInterestingAlloca (dl, *AI)) continue;
	    
	    if (dsa->shouldBeTrackedPtr (*AI, F, __LINE__))  {
	      B.SetInsertPoint (getNextInst (I));
	      SizeOffsetEvalType Data = size_offset_eval.compute (I);
	      if (Value* size = Data.first) {
		Value* vptr = B.CreateBitOrPointerCast (AI, geti8PtrTy (ctx));
		size = B.CreateZExtOrTrunc (size, intPtrTy);
		updateCallGraph (cg, &F, B.CreateCall2 (abc_alloc, vptr,size));
		if (PositiveAddresses) {
		  // Trick llvm to make sure that all pointer addresses
		  // are positive
		  updateCallGraph
		    (cg, &F, 
		     B.CreateCall (assumeFn,
				   B.CreateICmpSGT(vptr, createNullCst (ctx))));
		}
	      }
	    }
	  } else if (isMallocLikeFn(I, tli, true) || isOperatorNewLikeFn(I, tli, true)){
	    
	    if (dsa->shouldBeTrackedPtr (*I, F, __LINE__)) {
	      SizeOffsetEvalType Data = size_offset_eval.compute (I);
	      if (Value* size = Data.first) {
		B.SetInsertPoint (getNextInst (I));
		Value* vI = B.CreateBitOrPointerCast (I, geti8PtrTy (ctx));
		size = B.CreateZExtOrTrunc (size,intPtrTy);
		updateCallGraph (cg, &F,B.CreateCall2 (abc_alloc, vI,size));
		if (PositiveAddresses) {
		  // Trick llvm to make sure that all pointer addresses
		  // are positive
		  updateCallGraph
		    (cg, &F, 
		     B.CreateCall (assumeFn, 
				   B.CreateICmpSGT(vI,
						   createNullCst (ctx))));
		}
	      } else 
		errs () << "WARNING ABC: missing allocation site " << *I << "\n"; 
	    }
	  }
	}
      } 
    }
    
    errs () << " ========== ABC  ==========\n";
    errs () << "-- " << trivial_checks
	    << " Total number of trivially safe memory reads/writes (not instrumented)\n"
	    << "-- " << mem_accesses - trivial_checks
	    << " Total number of non-trivial memory reads/writes\n"
	    << "-- " << checks_added
	    << " Total number of memory reads/writes instrumented\n"; 
    
    if (TrackedDsaNode != 0) {
      errs () << "-- " << untracked_dsa_checks 
	      << " Total number of skipped checks because untracked Dsa node\n";
    }
    
    return true;
  }
  
  void GlobalCCallbacks::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<seahorn::DSAInfo>();    // run llvm dsa
    AU.addRequired<sea_dsa::DsaInfoPass>();// run seahorn dsa
    AU.addRequired<llvm::DataLayoutPass>();
    AU.addRequired<llvm::TargetLibraryInfo>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addRequired<llvm::CallGraphWrapperPass>();
  } 
  
  char GlobalCCallbacks::ID = 0;
  
  static llvm::RegisterPass<GlobalCCallbacks> 
  Z ("abc-global-c", "Insert array buffer checks using Global encoding by calling C functions");
  
} // end namespace seahorn
