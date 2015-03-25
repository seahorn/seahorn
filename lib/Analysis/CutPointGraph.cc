#include "seahorn/Analysis/CutPointGraph.hh"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h"
#include "boost/range.hpp"
#include "seahorn/Support/CFG.hh"

#include "avy/AvyDebug.h"
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

    LOG ("cpg", print (errs (), F.getParent ()));
    return false;
  }


  void CutPointGraph::computeCutPoints (const Function &F, const TopologicalOrder &topo)
  {

    for (const BasicBlock *bb : topo)
    {
      // -- skip basic blocks that are already marked as cut-points
      if (isCutPoint (*bb)) continue;
      
      // entry
      if (pred_begin (bb) == pred_end (bb))
      {
        LOG ("cpg", errs () << "entry cp: " << bb->getName () << "\n");
        newCp (*bb);
      }
      
      // exit
      if (succ_begin (bb) == succ_end (bb))
      {
        LOG ("cpg", errs () << "exit cp: " << bb->getName () << "\n");
        newCp (*bb);
      }
      

      // has incoming back-edge
      for (const BasicBlock *pred :
             boost::make_iterator_range (pred_begin (bb), pred_end (bb)))
        if (topo.isBackEdge (*pred, *bb))
        {
          LOG ("cpg", errs () << "back-edge cp: " << bb->getName () << "\n");
          newCp (*bb);
        }
      
    }

  }

  void setbit (llvm::BitVector &b, unsigned idx)
  {
    if (idx >= b.size ()) b.resize (idx + 1);
    b.set (idx);
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
