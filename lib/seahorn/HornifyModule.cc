#include "seahorn/HornifyModule.hh"


#include "ufo/Passes/NameValues.hpp"

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "seahorn/Support/BoostLlvmGraphTraits.hh"

#include "boost/range.hpp"
#include "boost/scoped_ptr.hpp"
#include "boost/optional.hpp"
#include <regex>

#include "seahorn/Support/SortTopo.hh"

#include "seahorn/SymStore.hh"
#include "seahorn/LiveSymbols.hh"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Analysis/CanFail.hh"
#include "ufo/Smt/EZ3.hh"
#include "ufo/Stats.hh"

#include "seahorn/HornifyFunction.hh"
#include "seahorn/FlatHornifyFunction.hh"
#include "seahorn/IncHornifyFunction.hh"

#ifdef HAVE_CRAB_LLVM
#include "crab_llvm/CrabLlvm.hh"
#endif

using namespace llvm;
using namespace seahorn;


static llvm::cl::opt<enum TrackLevel>
TL("horn-sem-lvl",
   llvm::cl::desc ("Track level for symbolic execution"),
   cl::values (clEnumValN (REG, "reg", "Primitive registers only"),
               clEnumValN (PTR, "ptr", "REG + pointers"),
               clEnumValN (MEM, "mem", "PTR + memory content"),
               clEnumValEnd),
   cl::init (seahorn::REG));


namespace hm_detail {enum Step {SMALL_STEP, LARGE_STEP,
                                CLP_SMALL_STEP, CLP_FLAT_SMALL_STEP,
                                FLAT_SMALL_STEP, FLAT_LARGE_STEP, INC_SMALL_STEP};}

static llvm::cl::opt<enum hm_detail::Step>
Step("horn-step",
     llvm::cl::desc ("Step to use for the encoding"),
     cl::values (clEnumValN (hm_detail::SMALL_STEP, "small", "Small Step"),
                 clEnumValN (hm_detail::LARGE_STEP, "large", "Large Step"),
                 clEnumValN (hm_detail::FLAT_SMALL_STEP, "fsmall", "Flat Small Step"),
                 clEnumValN (hm_detail::FLAT_LARGE_STEP, "flarge", "Flat Large Step"),
                 clEnumValN (hm_detail::CLP_SMALL_STEP, "clpsmall", "CLP Small Step"),
                 clEnumValN (hm_detail::CLP_FLAT_SMALL_STEP, "clpfsmall","CLP Flat Small Step"),
                 clEnumValN (hm_detail::INC_SMALL_STEP, "incsmall","Inconsistency Small Step"),
                 clEnumValEnd),
     cl::init (hm_detail::SMALL_STEP));

static llvm::cl::opt<bool>
InterProc("horn-inter-proc",
          llvm::cl::desc ("Use inter-procedural encoding"),
          cl::init (false));

static llvm::cl::opt<bool>
AbortOnRecursion("horn-abort-on-recursion",
                 llvm::cl::desc ("Abort if program has a recursive call"),
                 cl::init (false));

static llvm::cl::opt<bool>
NoVerification("horn-no-verif",
          llvm::cl::desc ("Generate only SMT2 encoding (i.e. even if there are no assertions)"),
          cl::init (false));

static llvm::cl::list<std::string>
AbstractFunctions("horn-abstract",
		  llvm::cl::desc("Abstract all calls to these functions"),
		  llvm::cl::ZeroOrMore);

namespace seahorn
{
  char HornifyModule::ID = 0;

  struct FunctionNameMatcher :
    public std::unary_function<const Function&, bool> {
    boost::optional <std::regex> m_re;
    FunctionNameMatcher (std::string s) { 
      if (s != "")
      {
  	try
  	{ m_re = std::regex (s);  }  
  	catch (std::regex_error& e) 
  	{ errs () << "Warning: syntax error in the regex: "
		  << e.what () << "\n"; }
      }
    }
    bool operator() (const Function &fn)  {
      if (!m_re) return false;  // this should not happen
      auto fn_name = fn.getName().str() ;  
      return std::regex_match (fn_name, *m_re);
    }
  };

  bool shouldBeAbstracted (const Function &fn) {
    for (auto name : AbstractFunctions) {
      FunctionNameMatcher filter (name);
      if (filter (fn)) return true;
    }
    return false;
  }

  HornifyModule::HornifyModule () :
    ModulePass (ID), m_zctx (m_efac),  m_db (m_efac),
    m_td(0), m_canFail(0)
  {
  }

  bool HornifyModule::runOnModule (Module &M)
  {
    ScopedStats _st ("HornifyModule");

    bool Changed = false;
    m_td = &getAnalysis<DataLayoutPass> ().getDataLayout ();
    m_canFail = getAnalysisIfAvailable<CanFail> ();

    typename UfoSmallSymExec::FunctionPtrSet abs_fns;
    if (!AbstractFunctions.empty ()) {
      for (auto &F: M)
	if (shouldBeAbstracted (F)) abs_fns.insert(&F);
    }
    
    if (Step == hm_detail::CLP_SMALL_STEP || 
        Step == hm_detail::CLP_FLAT_SMALL_STEP)
      m_sem.reset (new ClpSmallSymExec (m_efac, *this, TL));
    else
      m_sem.reset (new UfoSmallSymExec (m_efac, *this, TL, abs_fns));

    Function *main = M.getFunction ("main");
    if (!main)
    { // if not main found then program trivially safe
      errs () << "WARNING: main function not found so program is trivially safe.\n";
      m_db.addQuery (mk<FALSE> (m_efac));
      return Changed;
    }

    bool canFail = false;

    // --- optimizer or ms can detect an error and make main
    //     unreachable. In that case, it will insert a call to
    //     seahorn.fail.
    Function* failureFn = M.getFunction ("seahorn.fail");
    if (!canFail)
    {
      for (auto &I : boost::make_iterator_range (inst_begin(*main),
                                                 inst_end (*main)))
      {
        if (!isa<CallInst> (&I)) continue;
        // -- look through pointer casts
        Value *v = I.stripPointerCasts ();
        CallSite CS (const_cast<Value*> (v));
        const Function *fn = CS.getCalledFunction ();
        canFail |= (fn == failureFn);
      }
    }

    // --- we ask the can-fail analysis if no function can fail.
    if (!canFail)
    {
      Function* errorFn = M.getFunction ("verifier.error");
      for (auto &f : M)
      {
        if ((&f == errorFn) || (&f == failureFn))
          continue;
        canFail |= (m_canFail->canFail (&f));
      }
    }

    // --- no function can fail so the program is trivially safe.
    if (!canFail && !NoVerification)
    {
      errs () << "WARNING: no assertion was found ";
      errs () << "so either program does not have assertions or frontend discharged them.\n";
      m_db.addQuery (mk<FALSE> (m_efac));
      return Changed;
    }

    
    if (!NoVerification)
    {
      // --- expensive check that iterates over all callsites 
      Function* errorFn = M.getFunction ("verifier.error");            
      for (auto &fn: M)
	for (auto &I : boost::make_iterator_range (inst_begin(fn), inst_end(fn))) {
	  if (!isa<CallInst> (&I)) continue;
	  CallSite CS (&I);
	  const Function *callee = CS.getCalledFunction ();
	  if (callee == errorFn) {
	    // this happens when a function calls to verifier.error()
	    // but it is not reachable from main and for some reason
	    // (e.g., llvm.global_ctors) it was not marked as dead code.
	    errs () << "WARNING: found call to verifier.error(). This should not happen.\n";
	  }
	}
    }
    
    // create FunctionInfo for verifier.error() function
    if (Function* errorFn = M.getFunction ("verifier.error"))
    {
      FunctionInfo &fi = m_sem->getFunctionInfo (*errorFn);
      Expr boolSort = sort::boolTy (m_efac);
      ExprVector sorts (4, boolSort);
      fi.sumPred = bind::fdecl (mkTerm<const Function*> (errorFn, m_efac), sorts);
      m_db.registerRelation (fi.sumPred);

      // basic rules for error
      // error (false, false, false)
      // error (false, true, true)
      // error (true, false, true)
      // error (true, true, true)

      Expr trueE = mk<TRUE> (m_efac);
      Expr falseE = mk<FALSE> (m_efac);

      ExprSet allVars;

      ExprVector args {falseE, falseE, falseE};
      m_db.addRule (allVars, bind::fapp (fi.sumPred, args));

      args = {falseE, trueE, trueE} ;
      m_db.addRule (allVars, bind::fapp (fi.sumPred, args));

      args = {trueE, falseE, trueE} ;
      m_db.addRule (allVars, bind::fapp (fi.sumPred, args));

      args = {trueE, trueE, trueE} ;
      m_db.addRule (allVars, bind::fapp (fi.sumPred, args));

      args [0] = bind::boolConst (mkTerm (std::string ("arg.0"), m_efac));
      args [1] = bind::boolConst (mkTerm (std::string ("arg.1"), m_efac));
      args [2] = bind::boolConst (mkTerm (std::string ("arg.2"), m_efac));
      m_db.addConstraint (bind::fapp (fi.sumPred, args),
                          mk<AND> (mk<OR> (mk<NEG> (args [0]), args [2]),
                                   mk<OR> (args [0], mk<EQ> (args [1], args [2]))));
    }


    CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
    for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
    {
      const std::vector<CallGraphNode*> &scc = *it;
      CallGraphNode *cgn = scc.front ();
      Function *f = cgn->getFunction ();
      if (it.hasLoop () || scc.size () > 1)
      {
        errs () << "WARNING RECURSION at " << (f ? f->getName () : "nil") << "\n";
        errs () << "SCC is: ";
        for (auto sccn : scc)
        {
          Function *g = sccn->getFunction ();
          if (g) errs () << g->getName () << " ";
        }
        errs () << "\n";

        if (AbortOnRecursion)
        {
          errs () << "Aborting on recursion\n";
          std::exit (3);
        }
      }

      // assert (!it.hasLoop () && "Recursion not yet supported");
      // assert (scc.size () == 1 && "Recursion not supported");
      if (f) Changed = (runOnFunction (*f) || Changed);
    }

    if (!m_db.hasQuery ())
    {
      // --- This may happen if the exit block of main is unreachable
      //     but still the main function can fail.
      m_db.addQuery (mk<TRUE> (m_efac));
    }

    /**
       TODO:
         - name basic blocks so that there are no name clashes between functions (DONE)
         - handle new shadow mem functions in SymExec
         - add attributes (i.e., does not read memory) to shadow mem functions
         - factor out Live analysis from SymExec.
       To implement:

       1. walk up the call graph and compute live symbols

       2. from entry block of each function, compute globals that the
          function is using, and make it available to live analysis

       3. live analysis reads all globals that the function is using at a call site

       4. for non-trivial call graph scc

          a. run live analysis on each function
          b. merge live globals from all functions
          c. run one step of live analysis again with new global usage info

      At this point global liveness information is done

       5. update live values of entry blocks to include DSNodes that
          are passed in. This information is available from annotations
          in the return block left by the MemShadowDsaPass

       8. create summary predicates for functions. Use llvm::Function* as the name.
          Ensure that BasicBlocks and CutPoint include function in their name.
          Signature: live@entry (non-memory) , return val, memory regions

       7. use HornifyFunction to compute the system for each
          individual function Give it access to summary predicates so
          that it can deal with functions.  It will need to map
          parameters to arguments and globals to match live@entry part
          of the signature.

       8. Add rules connecting summaries. The rules are from return block.
           return_block(live@entry, live@other) & ret_block_actions ->
                           Summary (live@entry (non-memory), ret_val, memory)

       9. main is special:

            a. live at entry are globals and global memory
            b. entry rule is the initialization (i.e., all global values are 0 initially)
            c. query is whether main gets to its return location (same as UFO)

    */
    return Changed;
  }

  bool HornifyModule::runOnFunction (Function &F)
  {
    // -- skip functions without a body
    if (F.isDeclaration () || F.empty ()) return false;
    LOG("horn-step", errs () << "HornifyModule: runOnFunction: " << F.getName () << "\n");



    // XXX: between we run LiveSymbols and hornify function (see
    // below) the CFG can change because the construction of the
    // cutpoint graph calls a pass that unifies return nodes that
    // ultimately might change the CFG. 
    // 
    // This is a temporary hook to force computing the cutpoint graph
    // (and unifying return nodes) before computing liveness so that
    // we make sure the CFG does not change between LiveSymbols and
    // hornify function.
    /*CutPointGraph &cpg =*/ getAnalysis<CutPointGraph> (F);

    boost::scoped_ptr<HornifyFunction> hf (new SmallHornifyFunction
                                           (*this, InterProc));
    if (Step == hm_detail::LARGE_STEP)
      hf.reset (new LargeHornifyFunction (*this, InterProc));
    else if (Step == hm_detail::FLAT_SMALL_STEP ||
             Step == hm_detail::CLP_FLAT_SMALL_STEP)
      hf.reset (new FlatSmallHornifyFunction (*this, InterProc));
    else if (Step == hm_detail::FLAT_LARGE_STEP)
      hf.reset (new FlatLargeHornifyFunction (*this, InterProc));
    else if (Step == hm_detail::INC_SMALL_STEP)
        hf.reset (new IncSmallHornifyFunction (*this, InterProc));


    /// -- allocate LiveSymbols
    auto r = m_ls.insert (std::make_pair (&F, LiveSymbols (F, m_efac, *m_sem)));
    assert (r.second);
    /// -- run LiveSymbols
    r.first->second.run ();

    /// -- hornify function
    hf->runOnFunction (F);

    return false;
  }

  void HornifyModule::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<llvm::DataLayoutPass>();

    AU.addRequired<seahorn::CanFail> ();
    AU.addRequired<ufo::NameValues>();

    AU.addRequired<llvm::CallGraphWrapperPass> ();
    AU.addPreserved<llvm::CallGraphWrapperPass> ();

    AU.addRequired<seahorn::TopologicalOrder>();
    AU.addRequired<seahorn::CutPointGraph>();
#ifdef HAVE_CRAB_LLVM
    AU.addPreserved<crab_llvm::CrabLlvm> ();
#endif

  }

  const LiveSymbols& HornifyModule::getLiveSybols (const Function &F) const
  {
    auto it = m_ls.find (&F);
    assert (it != m_ls.end ());
    return it->second;
  }

  const Expr HornifyModule::bbPredicate (const BasicBlock &BB)
  {
    const BasicBlock *bb = &BB;
    Expr res = m_bbPreds [bb];
    if (res) return res;


    const ExprVector &lv = live (bb);
    ExprVector sorts;
    sorts.reserve (lv.size () + 1);

    for (auto &v : lv)
    {
      assert (bind::isFapp (v));
      assert (bind::domainSz (bind::fname (v)) == 0);
      sorts.push_back (bind::typeOf (v));
    }
    sorts.push_back (mk<BOOL_TY> (m_efac));

    Expr name = mkTerm (bb, m_efac);
    res = bind::fdecl (name, sorts);
    m_bbPreds [bb] = res;
    return res;
  }

  bool HornifyModule::isBbPredicate (Expr pred) const
  {
    Expr v = pred;
    if (bind::isFapp (v)) v = bind::fname (pred);
    if (!bind::isFdecl (v)) return false;
    v = bind::fname (v);
    return isOpX<BB> (v);
  }

  const BasicBlock& HornifyModule::predicateBb (Expr pred) const
  {
    Expr v = pred;
    if (bind::isFapp (v)) v = bind::fname (pred);

    assert (bind::isFdecl (v));
    v = bind::fname (v);
    assert (isOpX<BB> (v));
    return *getTerm<const BasicBlock*> (v);
  }

}
