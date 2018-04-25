#include "seahorn/Transforms/Instrumentation/ShadowMemSeaDsa.hh"

#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"

#include "avy/AvyDebug.h"
#include "boost/range.hpp"
#include "boost/range/algorithm/sort.hpp"
#include "boost/range/algorithm/set_algorithm.hpp"
#include "boost/range/algorithm/binary_search.hpp"

#include "sea_dsa/CallSite.hh"
#include "sea_dsa/Mapper.hh"
#include "sea_dsa/DsaAnalysis.hh"

static llvm::cl::opt<bool>
SplitFields("horn-sea-dsa-split",
            llvm::cl::desc("DSA: Split nodes by fields"),
            llvm::cl::init (false));

static llvm::cl::opt<bool>
LocalReadMod ("horn-sea-dsa-local-mod",
              llvm::cl::desc ("DSA: Compute read/mod info locally"),
              llvm::cl::init (false));

namespace seahorn
{
  using namespace llvm;
  using namespace sea_dsa;

  namespace sea_dsa_impl 
  {

    template <typename Set>
    void markReachableNodes (const Node *n, Set &set)
    {
      if (!n) return;
      assert (!n->isForwarding () && "Cannot mark a forwarded node");
      
      if (set.insert (n).second) 
        for (auto const &edg : n->links ())
          markReachableNodes (edg.second->getNode (), set);
    }

    template <typename Set>
    void reachableNodes (const Function &fn, Graph &g, Set &inputReach, Set& retReach)
    {
      // formal parameters
      for (Function::const_arg_iterator I = fn.arg_begin(), E = fn.arg_end(); I != E; ++I)
      {
        const Value &arg = *I;
        if (g.hasCell (arg)) 
        {
          Cell &c = g.mkCell (arg, Cell ());
          markReachableNodes (c.getNode (), inputReach);
        }
      }
      
      // globals
      for (auto &kv : boost::make_iterator_range (g.globals_begin (),
                                                  g.globals_end ()))
        markReachableNodes (kv.second->getNode (), inputReach);
      
      // return value
      if (g.hasRetCell (fn))
        markReachableNodes (g.getRetCell (fn).getNode(), retReach);
    }

    // template <typename Set>
    // void inputReachableNodes (const DSCallSite &cs, DSGraph &dsg, Set &set)
    // {
    //   markReachableNodes (cs.getVAVal().getNode (), set);
    //   if (cs.isIndirectCall ()) markReachableNodes (cs.getCalleeNode (), set);
    //   for (unsigned i = 0, e = cs.getNumPtrArgs (); i != e; ++i)
    //     markReachableNodes (cs.getPtrArg (i).getNode (), set);
    
    //   // globals
    //   DSScalarMap &sm = dsg.getScalarMap ();
    //   for (auto &gv : boost::make_iterator_range (sm.global_begin(), sm.global_end ()))
    //     markReachableNodes (sm[gv].getNode (), set);
    // }
  
    // template <typename Set>
    // void retReachableNodes (const DSCallSite &cs, Set &set) 
    // {markReachableNodes (cs.getRetVal ().getNode (), set);}
  
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
  
    // /// Computes DSNode reachable from the call arguments
    // /// reach - all reachable nodes
    // /// outReach - subset of reach that is only reachable from the return node
    // template <typename Set1, typename Set2>
    // void argReachableNodes (DSCallSite CS, DSGraph &dsg, 
    //                         Set1 &reach, Set2 &outReach)
    // {
    //   inputReachableNodes (CS, dsg, reach);
    //   retReachableNodes (CS, outReach);
    //   set_difference (outReach, reach);
    //   set_union (reach, outReach);
    // }


    /// Computes Node reachable from the call arguments in the graph.
    /// reach - all reachable nodes
    /// outReach - subset of reach that is only reachable from the return node
    template <typename Set1, typename Set2>
    void argReachableNodes (const Function &fn, Graph &G, 
                            Set1 &reach, Set2 &outReach)
    {
      reachableNodes (fn, G, reach, outReach);
    set_difference (outReach, reach);
    set_union (reach, outReach);
    }

  } // end namespace sea_dsa_impl


  bool ShadowMemSeaDsa::isRead (const Cell &c, const Function &f)
  {
    return c.getNode () ? isRead (c.getNode (), f) : false;
  }
  bool ShadowMemSeaDsa::isModified (const Cell &c, const Function &f)
  {
    return c.getNode () ? isModified (c.getNode (), f) : false;
  } 
  bool ShadowMemSeaDsa::isRead (const Node *n, const Function &f)
  {
    LOG("shadow_mod",
          if (LocalReadMod && n->isRead () != (m_readList[&f].count (n) > 0))
          {
            errs () << f.getName ()
                    << " readNode: " << n->isRead ()
                    << " readList: " << m_readList[&f].count(n) << "\n";
            if (n->isRead ()) n->write(errs ());
          }
        );
    
    return LocalReadMod ?  m_readList[&f].count(n) > 0 : n->isRead ();
  }
  bool ShadowMemSeaDsa::isModified (const Node *n, const Function &f)
  {
    LOG ("shadow_mod",
         if (LocalReadMod && n->isModified () != (m_modList[&f].count (n) > 0))
         {
           errs () << f.getName ()
                   << " modNode: " << n->isModified ()
                   << " modList: " << m_modList[&f].count(n) << "\n";
           if (n->isModified ()) n->write(errs());
         });
    return LocalReadMod ? m_modList[&f].count (n) > 0 : n->isModified ();
  }
  
  AllocaInst* ShadowMemSeaDsa::allocaForNode (const Node *n, const unsigned offset)
  {
    auto &offmap = m_shadows[n];
    
    auto it = offmap.find (offset);
    if (it != offmap.end ()) return it->second;
    
    AllocaInst *a = new AllocaInst (m_Int32Ty, 0);
    offmap [offset] = a;
    return a;
  }
    
  unsigned ShadowMemSeaDsa::getId (const Node *n, unsigned offset)
  {
    auto it = m_node_ids.find (n);
    if (it != m_node_ids.end ()) return it->second + offset;
    
    unsigned id = m_max_id;
    m_node_ids[n] = id;

    if (n->size() == 0) {
      // XXX: nodes can have zero size
      assert (offset == 0);
      m_max_id++;
      return id;
    }
    
    // -- allocate enough ids for every byte of the object
    assert (n->size() > 0);
    m_max_id += n->size ();
    return id + offset;
  }
    
    
  void ShadowMemSeaDsa::declareFunctions (llvm::Module &M)
  {
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
  }
  
  bool ShadowMemSeaDsa::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
  
    m_dsa = &getAnalysis<DsaAnalysis>().getDsaAnalysis ();
    
    if (LocalReadMod) computeReadMod ();
    
    declareFunctions(M);
    m_node_ids.clear ();
    for (Function &f : M) runOnFunction (f);
      
    return false;
  }
  
  void ShadowMemSeaDsa::computeReadMod ()
  {
    CallGraph &cg = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
    for (auto it = scc_begin (&cg); !it.isAtEnd(); ++it)
    {
      const std::vector<CallGraphNode*> &scc = *it;
      NodeSet read;
      NodeSet modified;

      // compute read/mod, sharing information between scc 
      for (CallGraphNode *cgn : scc)
      {
        Function *f = cgn->getFunction ();
        if (!f) continue;
        updateReadMod (*f, read, modified);
      }

      // set the computed read/mod to all functions in the scc
      for (CallGraphNode *cgn : scc)
      {
        Function *f = cgn->getFunction ();
        if (!f) continue;
        m_readList[f].insert (read.begin (), read.end ());
        m_modList[f].insert (modified.begin(), modified.end ());
      }
    }
  }
  
  void ShadowMemSeaDsa::updateReadMod (Function &F, NodeSet &readSet, NodeSet &modSet)
  {
    if (!m_dsa->hasGraph (F)) return;
    
    Graph &G = m_dsa->getGraph (F);
    for (BasicBlock &bb : F)
    {
      for (Instruction &inst : bb)
      {
        if (LoadInst *li = dyn_cast<LoadInst> (&inst))
        {
          if (G.hasCell (*(li->getPointerOperand ())))
          {
            const Cell &c = G.getCell (*(li->getPointerOperand ()));
            if (!c.isNull()) readSet.insert (c.getNode ());
          }
        }
        else if (StoreInst *si = dyn_cast<StoreInst> (&inst))
        {
          if (G.hasCell (*(si->getPointerOperand ())))
          {
            const Cell &c = G.getCell (*(si->getPointerOperand ()));
            if (!c.isNull()) modSet.insert (c.getNode ());
          }
        }
        else if (CallInst *ci = dyn_cast<CallInst> (&inst))
        {
          CallSite CS (ci);
          Function *cf = CS.getCalledFunction ();
          if (!cf) continue;
          if (cf->getName ().equals ("calloc"))
          {
            const Cell &c = G.getCell (inst);
            if (!c.isNull()) modSet.insert (c.getNode ());
          }
          else if (m_dsa->hasGraph (*cf))
          {            
            readSet.insert (m_readList[cf].begin (), m_readList[cf].end ());
            modSet.insert (m_modList[cf].begin (), m_modList[cf].end ());
          }            
          
        }
        // TODO: handle intrinsics (memset,memcpy) and other library functions
      }
    }
  }
  
  static Value *getUniqueScalar (LLVMContext &ctx, IRBuilder<> &B, const Cell &c)
  {
    const Node* n = c.getNode ();
    if (n && c.getOffset () == 0)
    {
      Value *v = const_cast<Value*>(n->getUniqueScalar ());
    
      // -- a unique scalar is a single-cell global variable. We might be
      // -- able to extend this to single-cell local pointers, but these
      // -- are probably not very common.
      if (v)
        if (GlobalVariable *gv = dyn_cast<GlobalVariable> (v))
          if (gv->getType ()->getElementType ()->isSingleValueType ())
            return B.CreateBitCast (v, Type::getInt8PtrTy (ctx));
    }
    return ConstantPointerNull::get (Type::getInt8PtrTy (ctx));
  }

  unsigned ShadowMemSeaDsa::getOffset (const Cell &c)
  {return (SplitFields ? c.getOffset() : 0);}    
  
  bool ShadowMemSeaDsa::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;
      
    if (!m_dsa->hasGraph(F)) return false;

    Graph &G = m_dsa->getGraph (F);

    LOG ("shadow",
         errs () << "Looking into globals\n";
         for (auto &kv: boost::make_iterator_range (G.globals_begin (),
                                                    G.globals_end ()))
         {
           errs () << "Node for: " << *kv.first << "\n";
           if (kv.second->getNode ()) errs () << *(kv.second);
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
          if (!G.hasCell (*(load->getOperand (0)))) continue;
          const Cell &c = G.getCell (*(load->getOperand (0)));
          if (c.isNull()) continue;
          
          B.SetInsertPoint (&inst);
          B.CreateCall (m_memLoadFn,
			{B.getInt32 (getId (c)),
                         B.CreateLoad (allocaForNode (c)),
			 getUniqueScalar (ctx, B, c)});
        }
        else if (const StoreInst *store = dyn_cast<StoreInst> (&inst))
        {
          if (!G.hasCell (*(store->getOperand (1)))) continue;
          const Cell &c = G.getCell (*(store->getOperand (1)));
          if (c.isNull()) continue;
          
          B.SetInsertPoint (&inst);
          AllocaInst *v = allocaForNode (c);
          B.CreateStore (B.CreateCall (m_memStoreFn, 
                                       {B.getInt32 (getId (c)),
                                        B.CreateLoad (v),
					getUniqueScalar (ctx, B, c)}),
                         v);           
        }
        else if (CallInst *call = dyn_cast<CallInst> (&inst))
        {
          /// ignore inline assembly
          if (call->isInlineAsm ()) continue;
          
          /// skip intrinsics, except for memory-related ones
          if (isa<IntrinsicInst> (call) && !isa<MemIntrinsic> (call)) continue;

          /// skip seahorn.* and verifier.* functions
          if (Function *fn = call->getCalledFunction ())
            if ((fn->getName ().startswith ("seahorn.") ||
                 fn->getName ().startswith ("verifier.")) &&
                /* seahorn.bounce should be treated as a regular function*/
                !(fn->getName ().startswith ("seahorn.bounce"))) 
              continue;

          LOG ("shadow_cs", errs () << "Call: " << *call << "\n";);

          ImmutableCallSite ICS(call);
          DsaCallSite CS (ICS);

          if (!CS.getCallee()) continue;
          
          if (CS.getCallee ()->getName ().equals ("calloc"))
          {
            if (!G.hasCell(*call)) continue;
            const Cell &c = G.getCell (*call);
            if (c.isNull()) continue;
            
	    if (c.getOffset () == 0) {
	      B.SetInsertPoint (call);
	      AllocaInst *v = allocaForNode (c);
	      B.CreateStore (B.CreateCall (m_memStoreFn,
					   {B.getInt32 (getId (c)),
					    B.CreateLoad (v),
					    getUniqueScalar (ctx, B, c)}), v);
	    } else {
	      // TODO: handle multiple nodes
	      errs () << "WARNING: missing calloc instrumentation because cell offset is not zero\n";
	    }
          }
          else if (MemSetInst *MSI = dyn_cast<MemSetInst>(&inst))
          {
	    Value &dst = *(MSI->getDest ());
	    
            if (!G.hasCell(dst)) continue;
            const Cell &c = G.getCell (dst);
            if (c.isNull()) continue;

	    if (c.getOffset () == 0) {
	      B.SetInsertPoint (&inst);
	      AllocaInst *v = allocaForNode (c);
	      B.CreateStore (B.CreateCall (m_memStoreFn,
					   {B.getInt32 (getId (c)),
					    B.CreateLoad (v),
					    getUniqueScalar (ctx, B, c)}), v);
	    } else {
	      // TODO: handle multiple nodes
	      errs () << "WARNING: missing memset instrumentation because cell offset is not zero\n";
	    }
          }
	  

          const Function &CF = *CS.getCallee ();
          
          if (!m_dsa->hasGraph (CF)) continue;
          
          Graph &calleeG= m_dsa->getGraph (CF);
          
          // -- compute callee nodes reachable from arguments and returns
          std::set<const Node*> reach;
          std::set<const Node*> retReach;
          sea_dsa_impl::argReachableNodes (CF, calleeG, reach, retReach);

          // -- compute mapping between callee and caller graphs
          SimulationMapper simMap;
          Graph::computeCalleeCallerMapping (CS, calleeG, G, simMap); 
          
          /// generate mod, ref, new function, based on whether the
          /// remote node reads, writes, or creates the corresponding node.
          
          B.SetInsertPoint (&inst);
          unsigned idx = 0;
          for (const Node* n : reach)
          {
            LOG("global_shadow", 
                errs () << *n << "\n";
                // n->print (errs (), n->getParentGraph ());
                // errs () << "global: " << n->isGlobalNode () << "\n";
                // errs () << "#globals: " << n->numGlobals () << "\n";
                // svset<const GlobalValue*> gv;
                // if (n->numGlobals () == 1) n->addFullGlobalsSet (gv);
                // errs () << "gv-size: " << gv.size () << "\n";
                // if (gv.size () == 1) errs () << "Global: " << *(*gv.begin ()) << "\n";
                const Value *v = n->getUniqueScalar ();
                if (v) 
                  errs () << "value: " << *n->getUniqueScalar () << "\n";
                else
                  errs () << "no unique scalar\n";
                );
            
            
            // skip nodes that are not read/written by the callee
            if (!isRead (n, CF) && !isModified (n, CF)) continue;

            // TODO: This must be done for every possible offset of the caller node,
            // TODO: not just for offset 0

            assert (n);
            Cell callerC = simMap.get(Cell(const_cast<Node*> (n), 0,
                                           sea_dsa::FieldType::NotImplemented()));
            assert (!callerC.isNull() && "Not found node in the simulation map");

            AllocaInst *v = allocaForNode (callerC);
            unsigned id = getId (callerC);
          
            // -- read only node ignore nodes that are only reachable
            // -- from the return of the function
            if (isRead (n, CF) && !isModified (n, CF) && retReach.count(n) <= 0)
            {
              B.CreateCall (m_argRefFn,
			    {B.getInt32 (id),
                             B.CreateLoad (v),
                             B.getInt32 (idx),
			     getUniqueScalar (ctx, B, callerC)});
            }
            // -- read/write or new node
            else if (isModified (n, CF))
            {
              // -- n is new node iff it is reachable only from the return node
              Constant* argFn = retReach.count (n) ? m_argNewFn : m_argModFn;
              B.CreateStore (B.CreateCall (argFn, 
                                           {B.getInt32 (id),
                                            B.CreateLoad (v),
                                            B.getInt32 (idx),
					    getUniqueScalar (ctx, B, callerC)}), v);
            }
            idx++;
          }
        }
        
      }
      
    // compute Nodes that escape because they are either reachable
    // from the input arguments or from returns
    std::set<const Node*> reach;
    std::set<const Node*> retReach;
    sea_dsa_impl::argReachableNodes (F, G, reach, retReach);
    
    // -- create shadows for all nodes that are modified by this
    // -- function and escape to a parent function
    for (const Node *n : reach)
      if (isModified (n, F) || isRead (n, F))
      {
        // TODO: allocate for all slices of n, not just offset 0
        allocaForNode (n, 0);
      }
    
    // allocate initial value for all used shadows
    DenseMap<const Node*, DenseMap<unsigned, Value*> > inits;
    B.SetInsertPoint (&*F.getEntryBlock ().begin ());
    for (auto it : m_shadows)
    {
      const Node *n = it.first;

      Constant *fn = reach.count (n) <= 0 ? m_memShadowInitFn : m_memShadowArgInitFn;
      
      for (auto jt : it.second)
      {
        // TODO: Types
        Cell c (const_cast<Node*> (n), jt.first, FieldType::NotImplemented());
        AllocaInst *a = jt.second;
        B.Insert (a, "shadow.mem");
        CallInst *ci;
        ci = B.CreateCall (fn, {B.getInt32 (getId (c)), getUniqueScalar (ctx, B, c)});
        inits[c.getNode()][getOffset(c)] = ci;
        B.CreateStore (ci, a);
      }
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
      exit = llvm::SplitBlock (exit, ret,
			       // these two passes will not be preserved if null
			       nullptr /*DominatorTree*/, nullptr /*LoopInfo*/);
      ret = exit->getTerminator ();
    }
    
    B.SetInsertPoint (ret);
    unsigned idx = 0;
    for (const Node* n : reach)
    {
      // TODO: extend to work with all slices
      Cell c (const_cast<Node*> (n), 0, FieldType::NotImplemented());

      // n is read and is not only return-node reachable (for
      // return-only reachable nodes, there is no initial value
      // because they are created within this function)
      if ((isRead (n, F) || isModified (n, F)) && retReach.count (n) <= 0)
      {
        assert (!inits[n].empty());
        /// initial value
        B.CreateCall (m_markIn,
                      {B.getInt32 (getId (c)),
                       inits[n][0], 
                       B.getInt32 (idx),
		       getUniqueScalar (ctx, B, c)});
      }
      
      if (isModified (n, F))
      {
        assert (!inits[n].empty());
        /// final value
        B.CreateCall (m_markOut, 
                      {B.getInt32 (getId (c)),
                       B.CreateLoad (allocaForNode (c)),
                       B.getInt32 (idx),
		       getUniqueScalar (ctx, B, c)});
      }
      ++idx;
    }
      
    return true;
  }
    
  void ShadowMemSeaDsa::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequiredTransitive<DsaAnalysis> ();    
    AU.addRequired<llvm::CallGraphWrapperPass>();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
  } 
    

  class StripShadowMem : public ModulePass 
  {
  public:
    static char ID;
    StripShadowMem () : ModulePass (ID) {} 

    virtual StringRef getPassName() const { return "StripShadowMem"; }
    
    virtual void getAnalysisUsage (AnalysisUsage &AU) const override
    {AU.setPreservesAll ();}
    
    virtual bool runOnModule (Module &M) override
    {
      std::vector<std::string> voidFnNames = 
        {"shadow.mem.load", "shadow.mem.arg.ref",
         "shadow.mem.in", "shadow.mem.out" };
      
      for (auto &name : voidFnNames)
      {
        Function *fn = M.getFunction (name);
        if (!fn) continue;
        
        while (!fn->use_empty ())
        {
          CallInst *ci = cast<CallInst> (fn->user_back ());
          Value *last = ci->getArgOperand (ci->getNumArgOperands () - 1);
          ci->eraseFromParent ();
          RecursivelyDeleteTriviallyDeadInstructions (last);
        }
      }

      std::vector<std::string> intFnNames =
        { "shadow.mem.store", "shadow.mem.init",
          "shadow.mem.arg.init", "shadow.mem.arg.mod"};
      Value *zero = ConstantInt::get (Type::getInt32Ty(M.getContext ()), 0);
      
      for (auto &name : intFnNames)
      {
        Function *fn = M.getFunction (name);
        if (!fn) continue;
        
        while (!fn->use_empty ())
        {
          CallInst *ci = cast<CallInst> (fn->user_back ());
          Value *last = ci->getArgOperand (ci->getNumArgOperands () - 1);
          ci->replaceAllUsesWith (zero);
          ci->eraseFromParent ();
          RecursivelyDeleteTriviallyDeadInstructions (last);
        }
      }
      
      return true;
    }
    
  };    
}

namespace seahorn
{
  char ShadowMemSeaDsa::ID = 0;
  char StripShadowMem::ID = 0;  
  Pass * createShadowMemSeaDsaPass () {return new ShadowMemSeaDsa ();}
  Pass * createStripShadowMemPass () {return new StripShadowMem ();}  
}

static llvm::RegisterPass<seahorn::ShadowMemSeaDsa> X ("shadow-sea-dsa", "Shadow DSA nodes");

static llvm::RegisterPass<seahorn::StripShadowMem> Y ("strip-shadow-dsa",
                                                      "Remove shadow.mem instrinsics");


