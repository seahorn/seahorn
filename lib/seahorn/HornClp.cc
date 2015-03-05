#include "seahorn/HornClp.hh"
#include "llvm/Support/CommandLine.h"

namespace seahorn
{
  using namespace expr;
  using namespace std;
  
  ClpHornify::ClpHornify (HornClauseDB &db, raw_ostream &OS): 
      m_os (OS),
      m_query (db.getQuery ())
  { 
    for (auto & rule : db.getRules ())
    {
      Expr f =  rule.body ();
      assert ((f->arity () == 2) && isOpX<IMPL> (f));
      Expr head = f->right ();
      Expr body = f->left ();
      ClpRule clp_rule (head);
      // TODO: normalize
      m_rules.push_back (clp_rule);
    }
  }
    
  void ClpHornify::write () const
  {
    // TODO
  }
}
