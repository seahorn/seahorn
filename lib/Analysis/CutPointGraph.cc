#include "seahorn/Analysis/CutPointGraph.hh"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Support/CFG.hh"

#include "boost/range.hpp"
#include "avy/AvyDebug.h"

enum ExtraCpHeuristics { H0, H1, H2};
static llvm::cl::opt<ExtraCpHeuristics>
ExtraCp("horn-extra-cps", 
        llvm::cl::desc("Generate additional cut-points"),
        llvm::cl::values(
            clEnumValN (H0, "h0", /*"none",*/ 
                        "None"),
            clEnumValN (H1, "h1", /*"backedge-src",*/ 
                        "Add block if source of a back-edge"),
            clEnumValN (H2, "h2", /*"more-reach-cp-than-children",*/ 
                        "Add block if it reaches more cutpoints than its successors"),
            clEnumValEnd),
        llvm::cl::init (H0));
            
namespace seahorn
{
  char CutPointGraph::ID = 0;

  
  void CutPointGraph::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<UnifyFunctionExitNodes> ();
    AU.addRequiredTransitive<TopologicalOrder> ();
  }


  bool CutPointGraph::runOnFunction (llvm::Function &F)
  {
    //LOG("seahorn", errs () << "CPG runOnFunction: " << F.getName () << "\n");

    const TopologicalOrder &topo = getAnalysis<TopologicalOrder> ();

    computeCutPoints (F, topo);
    computeFwdReach (F, topo);
    computeBwdReach (F, topo);
    computeEdges (F, topo);

    LOG ("cpg", 
         errs () << "Size of the CPG: " 
                 << m_cps.size ()  << " nodes and " 
                 << m_edges.size() << " edges.\n");

    LOG ("cpg", print (errs (), F.getParent ()));

    return false;
  }

  void setbit (llvm::BitVector &b, unsigned idx)
  {
    if (idx >= b.size ()) b.resize (idx + 1);
    b.set (idx);
  }

  bool lookup (const DenseMap<const BasicBlock*, unsigned>& cpMap, const BasicBlock* bb) {
    return (cpMap.find (bb) != cpMap.end ());
  }

  void addCpMap (DenseMap<const BasicBlock*, unsigned>& cpMap, const BasicBlock* bb){ 
    auto it = cpMap.find (bb);
    if (it == cpMap.end ()) {
      cpMap.insert (std::make_pair (bb, cpMap.size()));
    }
  }

  void CutPointGraph::computeCutPoints (const Function &F, const TopologicalOrder &topo)
  {
    // -- store temporarily cutpoints without the need of preserving
    //    topological ordering.
    DenseMap<const BasicBlock*, unsigned> cp_map;

    for (const BasicBlock *BB : topo) {

      // -- skip basic blocks that are already marked as cut-points if
      // -- ExtraCp == H1 is enabled, we might still find a new cutpoint
      // -- that points into this one
      if (ExtraCp != H1 && lookup (cp_map, BB)) continue;

      // entry
      if (pred_begin (BB) == pred_end (BB))
      {
        LOG ("cpg", errs () << "entry cp: " << BB->getName () << "\n");
        addCpMap (cp_map, BB);
      }
      
      // exit
      if (succ_begin (BB) == succ_end (BB))
      {
        LOG ("cpg", errs () << "exit cp: " << BB->getName () << "\n");
        addCpMap (cp_map, BB);
      }
      
      // has incoming back-edge
      for (const BasicBlock *pred :
             boost::make_iterator_range (pred_begin (BB), pred_end (BB)))
        if (topo.isBackEdge (*pred, *BB))
        {

          LOG ("cpg", errs () << "back-edge cp: " << BB->getName () << "\n");
          addCpMap (cp_map, BB);

          // -- make a source of a back edge that has multiple successors a cutpoint
          if (ExtraCp == H1 && succ_end(BB) - succ_begin(BB) > 1)
          {
            LOG("cpg", 
                errs () << "Adding (pred) cp: " << pred->getName () << "\n";);
            addCpMap (cp_map, pred);
          }
        }      
    }
    
    if (ExtraCp == H2) {
      // -- compute for a basic block cutpoint's ids it can forward reach.
      // XXX: We cannot use m_fwd since it has not been computed
      // yet. We could compute m_fwd while we add cutpoints but I
      // prefer not to do it for now.
      BlockBitMap fwd;
      for (auto it = topo.rbegin (), end = topo.rend (); it != end; ++it) {
        const BasicBlock *BB = *it;
        BitVector &r = fwd [BB];
        for (const BasicBlock *succ : succs (*BB))
          if (lookup (cp_map, succ)) setbit (r, cp_map [succ]);
          else r |= fwd [succ];
      }
      for (const BasicBlock *BB : topo) {
        if (!lookup (cp_map, BB) && succ_end(BB) - succ_begin(BB) > 1) {
          // -- make a block a cutpoint if it can forward reach more
          //    cutpoints thant its successors.
          unsigned reachCpSucc = 0;
          for (const BasicBlock *succ : succs (*BB))
            reachCpSucc = std::max (reachCpSucc, fwd [succ].count ());

          if (reachCpSucc > 0 && fwd [BB].count () > reachCpSucc) {
            LOG("cpg", 
                errs () << "Adding (reachMoreCp) cp: " << BB->getName () << "\n";);
            addCpMap (cp_map, BB);
          }
        }      
      }
    }

    // -- store permanently cutpoints preserving topological ordering
    for (const BasicBlock* BB: topo)
      if (lookup (cp_map, BB)) newCp (*BB); 
    
    cp_map.clear ();
  }

  void CutPointGraph::orderCutPoints (const Function &F, const TopologicalOrder &topo)
  {
    m_cps.clear ();
    // -- re-create m_cps in topological order
    for (const BasicBlock *bb : topo)
    {
      auto it = m_bb.find (bb);
      if (it == m_bb.end ()) continue;

      CutPointPtr cp = it->second;
      cp->setId (m_cps.size ());
      m_cps.push_back (cp);
    }
  }
  
  void CutPointGraph::computeFwdReach (const Function &F, const TopologicalOrder &topo)
  {
    for (auto it = topo.rbegin (), end = topo.rend (); it != end; ++it)
    {
      const BasicBlock *bb = *it;

      BitVector &r = m_fwd [bb];
      for (const BasicBlock *succ : succs (*bb))
      {
        if (isCutPoint (*succ))
          setbit (r, getCp (*succ).id ());
        else
          r |= m_fwd [succ];
      }
    }

  }

  void CutPointGraph::computeBwdReach (const Function &F, const TopologicalOrder &topo)
  {
    for (const BasicBlock *bb : topo)
    {
      BitVector &r = m_bwd [bb];
      
      const BasicBlock &BB = *bb;
      for (const BasicBlock *pred :
             boost::make_iterator_range (pred_begin (bb), pred_end (bb)))
      {
        if (topo.isBackEdge (*pred, BB)) continue;
        if (isCutPoint (*pred))
          setbit (r, getCp (*pred).id ());
        else
          r |= m_bwd [pred];
      }
    }

    for (const CutPoint &cp : boost::make_iterator_range (begin (), end ()))
    {
      const BasicBlock *bb = &cp.bb ();
      BitVector &r = m_bwd [bb];

      for (const BasicBlock *pred :
             boost::make_iterator_range (pred_begin (bb), pred_end (bb)))
      {
        if (! topo.isBackEdge (*pred, *bb)) continue;
        if (isCutPoint (*pred))
          setbit (r, getCp (*pred).id ());
        else
          r |= m_bwd [pred];
      }
    }
  }

  void CutPointGraph::computeEdges (const Function &F, const TopologicalOrder &topo)
  {
    for (const BasicBlock *bb : topo)
    {
      if (isCutPoint (*bb))
      {
        BitVector &r = m_fwd [bb];
        CutPoint &cp = getCp (*bb);
        for (int i = r.find_first (); i >= 0; i = r.find_next (i))
        {
          CpEdge &edg = newEdge (cp, *m_cps [i]);
          edg.push_back (bb);
        }
      }
      else
      {
        BitVector &b = m_bwd[bb];
        BitVector &f = m_fwd[bb];

        for (int i = b.find_first (); i >= 0; i = b.find_next (i))
          for (int j = f.find_first (); j >= 0; j = f.find_next (j))
            getEdge (*m_cps [i], *m_cps [j])->push_back (bb);
      }

    }

  }

  CpEdge* CutPointGraph::getEdge (CutPoint &s, CutPoint &d)
  {
    for (auto it = s.succ_begin (), end = s.succ_end (); it != end; ++it)
    {
      CpEdge *edg = *it;
      if (&(edg->target ()) == &d) return edg;
    }

    return NULL;
  }

  const CpEdge* CutPointGraph::getEdge (const CutPoint &s, const CutPoint &d) const
  {
    for (const CpEdge *edg : boost::make_iterator_range (s.succ_begin (),
                                                         s.succ_end ()))
      if (&(edg->target ()) == &d) return edg;
    return NULL;
  }

  void CutPointGraph::print (raw_ostream &out, const Module *m) const
  {
    out << "CPG BEGIN\n";

    for (auto it = begin (), ie = end (); it != ie; ++it)
    {
      const CutPoint& cp = *it;

      out << cp.bb ().getName () << "\n";
      for (auto jt = cp.succ_begin (), je = cp.succ_end (); jt != je; ++jt)
      {
        out << "  (";
        const CpEdge &edge = **jt;
        for (const BasicBlock &bb : edge) out << bb.getName () << " ";
        out << ") ";
        out << edge.target ().bb ().getName () << "\n";
      }
    }

    out << "CPG END\n";
  }

  bool CutPointGraph::isFwdReach (const CutPoint &cp, const BasicBlock &bb) const
  {
    if (&(cp.bb ()) == &bb) return true;

    // cannot reach another cut-point without getting to it
    if (isCutPoint (bb)) return false;

    auto it = m_bwd.find (&bb);
    assert (it != m_bwd.end ());

    unsigned sz = it->second.size ();
    unsigned id = cp.id ();
    if (sz == 0 || id >= sz) return false;
    return (it->second)[id];
  }

}
static llvm::RegisterPass<seahorn::CutPointGraph> X ("cpg", "Construct Cut Point Graph",
                                                     true, true);
