#include "seahorn/Bmc.hh"
#include "seahorn/UfoSymExec.hh"

namespace seahorn
{
  void BmcEngine::addCutPoint (const CutPoint &cp)
  {
    if (m_cps.empty ())
    {
      m_cpg = &cp.parent ();
      m_fn = cp.bb ().getParent ();
    }
  
    assert (m_cpg == &cp.parent ());
    m_cps.push_back (&cp);
  }

  boost::tribool BmcEngine::solve ()
  {
    encode ();
    //m_result =  m_solver.solve ();
    return m_result;
  }

  void BmcEngine::encode ()
  {
    
    // -- only run the encoding once
    if (!m_side.empty ()) return;
    
    assert (m_cpg);
    assert (m_fn);
    UfoLargeSymExec sexec (m_sem);
    m_states.push_back (SymStore (m_efac));
    
    const CutPoint *prev = &m_cpg->getCp (m_fn->getEntryBlock ());
    for (const CutPoint *cp : m_cps)
    {
      m_states.push_back (m_states.back ());
      SymStore &s = m_states.back ();
      
      const CpEdge *edg = m_cpg->getEdge (*prev, *cp);
      assert (edg);
      m_edges.push_back (edg);
      sexec.execCpEdg (s, *edg, m_side);
      
      prev = cp;
    }
    
    //for (Expr v : m_side) m_solver.assertExpr (v);
    
  }

  void BmcEngine::reset ()
  {
    m_cps.clear ();
    m_cpg = nullptr;
    m_fn = nullptr;
    m_smt.reset ();

    m_side.clear ();
    m_states.clear ();
    m_edges.clear ();
  }
  
  
}
