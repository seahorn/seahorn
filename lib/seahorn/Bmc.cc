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
    // m_result =  m_solver.solve ();
    return m_result;
  }

  void BmcEngine::encode ()
  {
    // -- only run encoding once
    if (!m_side.empty ()) return;
    
    UfoLargeSymExec sexec (m_sem);
    m_states.push_back (SymStore (m_efac));
    // XXX TODO 
    
    
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
