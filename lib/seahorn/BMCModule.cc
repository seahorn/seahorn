#include "seahorn/BMCModule.hh"



#include "ufo/Passes/NameValues.hpp"

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "llvm/Analysis/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "seahorn/Support/BoostLlvmGraphTraits.hh"

#include "boost/range.hpp"
#include "boost/scoped_ptr.hpp"

#include "seahorn/SymStore.hh"
#include "seahorn/Support/SortTopo.hh"
#include "seahorn/LiveSymbols.hh"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Analysis/CanFail.hh"
#include "ufo/Smt/EZ3.hh"

#include "seahorn/BMCFunction.hh"

using namespace llvm;
using namespace seahorn;
using namespace seabmc;

static llvm::cl::opt<enum TrackLevel>
TL("horn-sem-lvl",
   llvm::cl::desc ("Track level for symbolic execution"),
   cl::values (clEnumValN (REG, "reg", "Primitive registers only"),
               clEnumValN (PTR, "ptr", "REG + pointers"),
               clEnumValN (MEM, "mem", "PTR + memory content"),
               clEnumValEnd),
   cl::init (seahorn::REG));


//namespace hm_detail {enum Step {SMALL_STEP, LARGE_STEP};}

// static llvm::cl::opt<enum hm_detail::Step>
// Step("horn-step",
//      llvm::cl::desc ("Step to use for the encoding"),
//      cl::values (clEnumValN (hm_detail::SMALL_STEP, "small", "Small Step"),
//                  clEnumValN (hm_detail::LARGE_STEP, "large", "Large Step"),
//                  clEnumValEnd),
//      cl::init (hm_detail::SMALL_STEP));


namespace seabmc
{
  char BMCModule::ID = 0;

  BMCModule::BMCModule () :
    ModulePass (ID), m_zctx (m_efac), m_fp (m_zctx),
    m_td(0)
  {
    // if (PdrVerbose > 0)
    //   z3n_set_param ("verbose", PdrVerbose);
    // -- disable slicing so that we can use cover
    ZParams<EZ3> params (m_zctx);
    // params.set (":slice", false);
    // params.set (":engine", PdrEngine);
    // params.set (":use-farkas", true);
    // params.set (":generate-proof-trace", false);
    // params.set (":inline-linear", false);
    // params.set (":inline-eager", false);
    m_fp.set (params);
  }

    bool BMCModule::runOnModule (Module &M)
    {
        LOG("bmc", errs () << "BMCModule: runOnModule\n");
        //ScopedStats _st ("HornifyModule");

        bool Changed = false;
        m_td = &getAnalysis<DataLayoutPass> ().getDataLayout ();

        CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
        for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
        {
            const std::vector<CallGraphNode*> &scc = *it;
            CallGraphNode *cgn = scc.front ();
            Function *f = cgn->getFunction ();
            if (it.hasLoop () || scc.size () > 1)
                errs () << "WARNING RECURSION at " << (f ? f->getName () : "nil") << "\n";
            // assert (!it.hasLoop () && "Recursion not yet supported");
            // assert (scc.size () == 1 && "Recursion not supported");
            if (f) Changed = (runOnFunction (*f) || Changed);
        }
        return Changed;
    }

  bool BMCModule::runOnFunction (Function &F)
  {
    // -- skip functions without a body
    if (F.isDeclaration () || F.empty ()) return false;
    LOG("bmc", errs () << "runOnFunction: " << F.getName () << "\n");

    //CutPointGraph &cpg = getAnalysis<CutPointGraph> (F);
    boost::scoped_ptr<BMCFunction> hf;
    hf.reset (new LargeBMCFunction (*this));

    /// -- allocate LiveSymbols
    auto r = m_ls.insert (std::make_pair (&F, LiveSymbols (F, m_efac, *m_sem)));
    assert (r.second);
    /// -- run LiveSymbols
    r.first->second.run ();

    /// -- bmc function
    hf->runOnFunction (F);

    return false;
  }

  void BMCModule::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
      AU.setPreservesAll ();
      AU.addRequired<llvm::DataLayoutPass>();

      AU.addRequired<seahorn::CanFail> ();
      AU.addRequired<ufo::NameValues>();

      AU.addRequired<llvm::CallGraphWrapperPass> ();
      AU.addPreserved<llvm::CallGraphWrapperPass> ();

      AU.addRequired<seahorn::TopologicalOrder>();
      AU.addRequired<seahorn::CutPointGraph>();

  }

  const LiveSymbols& BMCModule::getLiveSybols (const Function &F) const
  {
    auto it = m_ls.find (&F);
    assert (it != m_ls.end ());
    return it->second;
  }

  const Expr BMCModule::bbPredicate (const BasicBlock &BB)
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

  const BasicBlock& BMCModule::predicateBb (Expr pred) const
  {
    Expr v = pred;
    if (bind::isFapp (v)) v = bind::fname (pred);

    assert (bind::isFdecl (v));
    v = bind::fname (v);
    assert (isOpX<BB> (v));
    return *getTerm<const BasicBlock*> (v);
  }

}
