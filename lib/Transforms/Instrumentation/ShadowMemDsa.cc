#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#ifdef HAVE_DSA
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"

#include "seahorn/Support/SeaDebug.h"
#include "boost/range.hpp"
#include "boost/range/algorithm/sort.hpp"
#include "boost/range/algorithm/set_algorithm.hpp"
#include "boost/range/algorithm/binary_search.hpp"

#include "dsa/Steensgaard.hh"
// To print stats about llvm dsa
#include "seahorn/Support/DSAInfo.hh"

namespace seahorn
{
  using namespace llvm;
  
  template <typename Set>
  void markReachableNodes (const DSNode *n, Set &set)
  {
    if (!n) return;
    
    assert (!n->isForwarding () && "Cannot mark a forwarded node");
    if (set.insert (n).second)
      for (auto &edg : boost::make_iterator_range (n->edge_begin (), n->edge_end ()))
        markReachableNodes (edg.second.getNode (), set);
  }
  
  template <typename Set>
  void inputReachableNodes (const DSCallSite &cs, DSGraph &dsg, Set &set)
  {
    markReachableNodes (cs.getVAVal().getNode (), set);
    if (cs.isIndirectCall ()) markReachableNodes (cs.getCalleeNode (), set);
    for (unsigned i = 0, e = cs.getNumPtrArgs (); i != e; ++i)
      markReachableNodes (cs.getPtrArg (i).getNode (), set);
    
    // globals
    DSScalarMap &sm = dsg.getScalarMap ();
    for (auto &gv : boost::make_iterator_range (sm.global_begin(), sm.global_end ()))
      markReachableNodes (sm[gv].getNode (), set);
  }
  
  template <typename Set>
  void retReachableNodes (const DSCallSite &cs, Set &set) 
  {markReachableNodes (cs.getRetVal ().getNode (), set);}
  
  template <typename Set>
  void set_difference (Set &s1, Set &s2)
  {
    Set s3;
    boost::set_difference (s1, s2, std::inserter (s3, s3.end ()));
    std::swap (s3, s1);
  }
  
  template <typename Set>
  void set_union (Set &s1, Set &s2)
  {
    Set s3;
    boost::set_union (s1, s2, std::inserter (s3, s3.end ()));
    std::swap (s3, s1);
  }
  
  /// Computes DSNode reachable from the call arguments
  /// reach - all reachable nodes
  /// outReach - subset of reach that is only reachable from the return node
  template <typename Set1, typename Set2>
  void argReachableNodes (DSCallSite CS, DSGraph &dsg, 
                          Set1 &reach, Set2 &outReach)
  {
    inputReachableNodes (CS, dsg, reach);
    retReachableNodes (CS, outReach);
    set_difference (outReach, reach);
    set_union (reach, outReach);
  }
  
  
  
  AllocaInst* ShadowMemDsa::allocaForNode (const DSNode *n)
  {
    auto it = m_shadows.find (n);
    if (it != m_shadows.end ()) return it->second;
      
    AllocaInst *a = new AllocaInst (m_Int32Ty, 0);
    m_shadows [n] = a;
    return a;
  }
    
  unsigned ShadowMemDsa::getId (const DSNode *n)
  {
    auto it = m_node_ids.find (n);
    if (it != m_node_ids.end ()) return it->second;
    unsigned id = m_node_ids.size ();
    m_node_ids[n] = id;
    return id;
  }
    
    
  
  bool ShadowMemDsa::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
      
      
    //m_dsa = &getAnalysis<EQTDDataStructures> ();
    m_dsa = &getAnalysis<SteensgaardDataStructures> ();
    
    LLVMContext &ctx = M.getContext ();
    m_Int32Ty = Type::getInt32Ty (ctx);
    m_memLoadFn = M.getOrInsertFunction ("shadow.mem.load", 
                                         Type::getVoidTy (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt8PtrTy (ctx));
    
    
    m_memStoreFn = M.getOrInsertFunction ("shadow.mem.store", 
                                          Type::getInt32Ty (ctx),
                                          Type::getInt32Ty (ctx),
                                          Type::getInt32Ty (ctx),
                                          Type::getInt8PtrTy (ctx));
      
    m_memShadowInitFn = M.getOrInsertFunction ("shadow.mem.init",
                                               Type::getInt32Ty (ctx),
                                               Type::getInt32Ty (ctx),
                                               Type::getInt8PtrTy (ctx));
    
    m_memShadowArgInitFn = M.getOrInsertFunction ("shadow.mem.arg.init",
                                                  Type::getInt32Ty (ctx),
                                                  Type::getInt32Ty (ctx),
                                                  Type::getInt8PtrTy (ctx));
    
    m_argRefFn = M.getOrInsertFunction ("shadow.mem.arg.ref",
                                        Type::getVoidTy (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt8PtrTy (ctx));
    
     m_argModFn = M.getOrInsertFunction ("shadow.mem.arg.mod",
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt8PtrTy (ctx));
     m_argNewFn = M.getOrInsertFunction ("shadow.mem.arg.new",
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt32Ty (ctx),
                                         Type::getInt8PtrTy (ctx));
    
     m_markIn = M.getOrInsertFunction ("shadow.mem.in",
                                       Type::getVoidTy (ctx),
                                       Type::getInt32Ty (ctx),
                                       Type::getInt32Ty (ctx),
                                       Type::getInt32Ty (ctx),
                                       Type::getInt8PtrTy (ctx));
     m_markOut = M.getOrInsertFunction ("shadow.mem.out",
                                        Type::getVoidTy (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt32Ty (ctx),
                                        Type::getInt8PtrTy (ctx));
     m_node_ids.clear ();
     for (Function &f : M) runOnFunction (f);
      
     return false;
  }
  
  static Value *getUniqueScalar (LLVMContext &ctx, IRBuilder<> &B, const DSNode *n)
  {
    Value *v = const_cast<Value*>(n->getUniqueScalar ());
    
    // -- a unique scalar is a single-cell global variable. We might be
    // -- able to extend this to single-cell local pointers, but these
    // -- are probably not very common.
    if (v)
      if (GlobalVariable *gv = dyn_cast<GlobalVariable> (v))
        if (gv->getType ()->getElementType ()->isSingleValueType ())
          return B.CreateBitCast (v, Type::getInt8PtrTy (ctx));
    
    return ConstantPointerNull::get (Type::getInt8PtrTy (ctx));
  }
  
  bool ShadowMemDsa::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;
      
    DSGraph* dsg = m_dsa->getDSGraph (F);
    if (!dsg) return false;
    DSGraph* gDsg = dsg->getGlobalsGraph ();
    
    DSScalarMap &SM = dsg->getScalarMap ();
    LOG ("shadow",
         errs () << "Looking into globals\n";
         for (const Value* v : boost::make_iterator_range (SM.global_begin (),
                                                           SM.global_end ()))
         {
           DSNodeHandle lN = SM[v];
           errs () << "Node for: " << *v << "\n";
           if (lN.getNode ()) lN.getNode ()->dump ();
           else errs () << "NULL\n";
         }
         errs () << "End of globals\n";);
    
    
    
    m_shadows.clear ();
    // -- preserve ids across functions m_node_ids.clear ();
      
    LLVMContext &ctx = F.getContext ();
    IRBuilder<> B (ctx);
      
    for (BasicBlock &bb : F)
      for (Instruction &inst : bb)
      {
        if (const LoadInst *load = dyn_cast<LoadInst> (&inst))
        {
          DSNode* n = dsg->getNodeForValue (load->getOperand (0)).getNode ();
          if (!n) n = gDsg->getNodeForValue (load->getOperand (0)).getNode ();
          if (!n) continue;
          
          B.SetInsertPoint (&inst);
          B.CreateCall (m_memLoadFn,
			{B.getInt32 (getId (n)),
			 B.CreateLoad (allocaForNode (n)),
			 getUniqueScalar (ctx, B, n)});
        }
        else if (const StoreInst *store = dyn_cast<StoreInst> (&inst))
        {
          DSNode* n = dsg->getNodeForValue (store->getOperand (1)).getNode ();
          if (!n) n = gDsg->getNodeForValue (store->getOperand (1)).getNode ();
          if (!n) continue;
          B.SetInsertPoint (&inst);
          AllocaInst *v = allocaForNode (n);
          B.CreateStore (B.CreateCall (m_memStoreFn, 
                                       {B.getInt32 (getId (n)),
                                        B.CreateLoad (v),
					getUniqueScalar (ctx, B, n)}),
                         v);           
        }
        else if (CallInst *call = dyn_cast<CallInst> (&inst))
        {
          /// ignore inline assembly
          if (call->isInlineAsm ()) continue;
          
          /// skip intrinsics, except for memory-related ones
          if (isa<IntrinsicInst> (call) && !isa<MemIntrinsic> (call)) continue;

          /// skip sehaorn.* and verifier.* functions
          if (Function *fn = call->getCalledFunction ())
            if ((fn->getName ().startswith ("seahorn.") ||
                 fn->getName ().startswith ("verifier.")) &&
                /* seahorn.bounce should be treated as a regular function*/
                !(fn->getName ().startswith ("seahorn.bounce"))) 
              continue;
          

          LOG ("shadow_cs", errs () << "Call: " << *call << "\n";);
          DSCallSite CS = dsg->getDSCallSiteForCallSite (CallSite (call));
          if (!CS.isDirectCall ()) continue;

          if (!CS.getCalleeFunc ()) continue;
          
          if (CS.getCalleeFunc ()->getName ().equals ("calloc"))
          {
            DSNode* n = dsg->getNodeForValue (call).getNode ();
            if (!n) continue;
            B.SetInsertPoint (call);
            AllocaInst *v = allocaForNode (n);
            B.CreateStore (B.CreateCall (m_memStoreFn,
                                         {B.getInt32 (getId (n)),
                                          B.CreateLoad (v),
					  getUniqueScalar (ctx, B, n)}),
                           v);
          }
          
          if (!m_dsa->hasDSGraph (*CS.getCalleeFunc ())) continue;
          
          
          const Function &CF = *CS.getCalleeFunc ();
          DSGraph *cdsg = m_dsa->getDSGraph (CF);
          if (!cdsg) continue;
          
          // -- compute callee nodes reachable from arguments and returns
          DSCallSite CCS = cdsg->getCallSiteForArguments (CF);
          std::set<const DSNode*> reach;
          std::set<const DSNode*> retReach;
          argReachableNodes (CCS, *cdsg, reach, retReach);
          
          DSGraph::NodeMapTy nodeMap;
          dsg->computeCalleeCallerMapping (CS, CF, *cdsg, nodeMap);
          
          /// generate mod, ref, new function, based on whether the
          /// remote node reads, writes, or creates the corresponding node.
          
          B.SetInsertPoint (&inst);
          unsigned idx = 0;
          for (const DSNode* n : reach)
          {
            LOG("global_shadow", n->print (errs (), n->getParentGraph ());
                errs () << "global: " << n->isGlobalNode () << "\n";
                errs () << "#globals: " << n->numGlobals () << "\n";
                svset<const GlobalValue*> gv;
                if (n->numGlobals () == 1) n->addFullGlobalsSet (gv);
                errs () << "gv-size: " << gv.size () << "\n";
                if (gv.size () == 1) errs () << "Global: " << *(*gv.begin ()) << "\n";
                const Value *v = n->getUniqueScalar ();
                if (v) 
                  errs () << "value: " << *n->getUniqueScalar () << "\n";
                else
                  errs () << "no unique scalar\n";
                );
            
            
            // skip nodes that are not read/written by the callee
            if (!n->isReadNode () && !n->isModifiedNode ()) continue;

            /// XXX: it seems that for some nodes in the caller graph
            /// we may be unable to find its corresponding node in the
            /// callee graph.
            ///
            /// Since the current DSA implementation enforces that the
            /// caller and callee graphs are actually the same we can
            /// return n. Note that this is a hook and needs to be
            /// properly fixed.
            const DSNode* m = n;
            auto nodeMapIt = nodeMap.find (n);
            if (nodeMapIt != nodeMap.end ())
              m = nodeMapIt->second.getNode ();
             
            AllocaInst *v = allocaForNode (m);
            unsigned id = getId (m);
            
            // -- read only node ignore nodes that are only reachable
            // -- from the return of the function
            if (n->isReadNode () && !n->isModifiedNode () && retReach.count(n) <= 0)
              B.CreateCall (m_argRefFn,
			    {B.getInt32 (id),
			     B.CreateLoad (v),
                             B.getInt32 (idx),
			     getUniqueScalar (ctx, B, n)});
            // -- read/write or new node
            else if (n->isModifiedNode ())
            {
              // -- n is new node iff it is reachable only from the return node
              Constant* argFn = retReach.count (n) ? m_argNewFn : m_argModFn;
              B.CreateStore (B.CreateCall (argFn, 
					   {B.getInt32 (id),
                                            B.CreateLoad (v),
                                            B.getInt32 (idx),
					    getUniqueScalar (ctx, B, n)}), v);
            }
            idx++;
          }
        }
        
      }
      
    DSCallSite CS = dsg->getCallSiteForArguments (F);
    
    // compute DSNodes that escape because they are either reachable
    // from the input arguments or from returns
    std::set<const DSNode*> reach;
    std::set<const DSNode*> retReach;
    argReachableNodes (CS, *dsg, reach, retReach);
    
    // -- create shadows for all nodes that are modified by this
    // -- function and escape to a parent function
    for (const DSNode *n : reach)
      if (n->isModifiedNode () || n->isReadNode ()) allocaForNode (n); 
    
    // allocate initial value for all used shadows
    DenseMap<const DSNode*, Value*> inits;
    B.SetInsertPoint (&*F.getEntryBlock ().begin ());
    for (auto it : m_shadows)
    {
      const DSNode *n = it.first;
      AllocaInst *a = it.second;
      B.Insert (a, "shadow.mem");
      CallInst *ci;
      Constant *fn = reach.count (n) <= 0 ? m_memShadowInitFn : m_memShadowArgInitFn;
      ci = B.CreateCall (fn, {B.getInt32 (getId (n)), getUniqueScalar (ctx, B, n)});
      inits[n] = ci;
      B.CreateStore (ci, a);
    }
     
    UnifyFunctionExitNodes &ufe = getAnalysis<llvm::UnifyFunctionExitNodes> (F);
    BasicBlock *exit = ufe.getReturnBlock ();
    
    if (!exit) 
    {
      // XXX Need to think how to handle functions that do not return in 
      // XXX interprocedural encoding. For now, we print a warning and ignore this case.
      errs () << "WARNING: ShadowMem: function `" << F.getName () << "' never returns\n";
      return true;
    }
    
    assert (exit);
    TerminatorInst *ret = exit->getTerminator ();
    assert (ret);
    
    // split return basic block if it has more than just the return instruction
    if (exit->size () > 1)
    {
      exit = llvm::SplitBlock (exit, ret, nullptr /*DominatorTree not updated*/);
      ret = exit->getTerminator ();
    }
    
    B.SetInsertPoint (ret);
    unsigned idx = 0;
    for (const DSNode* n : reach)
    {
      // n is read and is not only return-node reachable (for
      // return-only reachable nodes, there is no initial value
      // because they are created within this function)
      if ((n->isReadNode () || n->isModifiedNode ()) 
          && retReach.count (n) <= 0)
      {
        assert (inits.count (n));
        /// initial value
        B.CreateCall (m_markIn,
                      {B.getInt32 (getId (n)),
                       inits[n], 
                       B.getInt32 (idx),
		       getUniqueScalar (ctx, B, n)});
      }
      
      if (n->isModifiedNode ())
      {
        assert (inits.count (n));
        /// final value
        B.CreateCall (m_markOut, 
                      {B.getInt32 (getId (n)),
                       B.CreateLoad (allocaForNode (n)),
                       B.getInt32 (idx),
		       getUniqueScalar (ctx, B, n)});
      }
      ++idx;
    }
      
    return true;
  }
    
  void ShadowMemDsa::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<seahorn::DSAInfo>(); // print stats about llvm dsa        
    // AU.addRequiredTransitive<llvm::EQTDDataStructures>();
    AU.addRequiredTransitive<llvm::SteensgaardDataStructures> ();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addPreserved<llvm::UnifyFunctionExitNodes>();
  } 
    
  //// XXX: Defined already in ShadowMemSeaDsa
  // class StripShadowMem : public ModulePass 
  // {
  // public:
  //   static char ID;
  //   StripShadowMem () : ModulePass (ID) {} 

  //   void getAnalysisUsage (AnalysisUsage &AU) const override
  //   {AU.setPreservesAll ();}
    
  //   bool runOnModule (Module &M) override
  //   {
  //     std::vector<std::string> voidFnNames = 
  //       {"shadow.mem.load", "shadow.mem.arg.ref",
  //        "shadow.mem.in", "shadow.mem.out" };
      
  //     for (auto &name : voidFnNames)
  //     {
  //       Function *fn = M.getFunction (name);
  //       if (!fn) continue;
        
  //       while (!fn->use_empty ())
  //       {
  //         CallInst *ci = cast<CallInst> (fn->user_back ());
  //         Value *last = ci->getArgOperand (ci->getNumArgOperands () - 1);
  //         ci->eraseFromParent ();
  //         RecursivelyDeleteTriviallyDeadInstructions (last);
  //       }
  //     }

  //     std::vector<std::string> intFnNames =
  //       { "shadow.mem.store", "shadow.mem.init",
  //         "shadow.mem.arg.init", "shadow.mem.arg.mod"};
  //     Value *zero = ConstantInt::get (Type::getInt32Ty(M.getContext ()), 0);
      
  //     for (auto &name : intFnNames)
  //     {
  //       Function *fn = M.getFunction (name);
  //       if (!fn) continue;
        
  //       while (!fn->use_empty ())
  //       {
  //         CallInst *ci = cast<CallInst> (fn->user_back ());
  //         Value *last = ci->getArgOperand (ci->getNumArgOperands () - 1);
  //         ci->replaceAllUsesWith (zero);
  //         ci->eraseFromParent ();
  //         RecursivelyDeleteTriviallyDeadInstructions (last);
  //       }
  //     }
      
  //     return true;
  //   }
    
  // };    
}

#endif

namespace seahorn
{
  char ShadowMemDsa::ID = 0;
  Pass * createShadowMemDsaPass () {return new ShadowMemDsa ();}
  //// XXX: Defined already in ShadowMemSeaDsa
  // char StripShadowMem::ID = 0;  
  // Pass * createStripShadowMemPass () {return new StripShadowMem ();}
  
}

static llvm::RegisterPass<seahorn::ShadowMemDsa> X ("shadow-dsa", "Shadow DSA nodes");
//// XXX: Defined already in ShadowMemSeaDsa
//static llvm::RegisterPass<seahorn::StripShadowMem> Y ("strip-shadow-dsa",
//                                                      "Remove shadow.mem instrinsics");

