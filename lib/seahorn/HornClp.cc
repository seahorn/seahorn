#include "seahorn/HornClp.hh"
#include "llvm/Support/CommandLine.h"

namespace seahorn
{
  using namespace expr;
  using namespace std;
  
  ClpHornify::ClpHornify (HornClauseDB &db): m_query (db.getQuery ())
  { 
    ///////
    // TODO:
    ////////
    // - all variables and predicate names must be translated to CLP
    //   format (e.g. all variables start with upper case etc)
    // - replace all fapp (p x y z) with p (x,y,z)
    // - replace all f <-> cond 
    // - support disjunctions (;) in the body 
    // - ignore (abstract) any constraint that is not supported by
    //   standard CLP (e.g., nonlinear)

    for (auto & rule : db.getRules ())
    {
      Expr f =  rule.body ();

      if (bind::isFapp (f))
        m_rules.push_back (ClpRule (f));
      else
      {
        if (!((f->arity () == 2) && isOpX<IMPL> (f)))
        { 
          cout << "Warning: hornClp ignoring clause " << *f << "\n"; 
          continue; 
        }

        assert (((f->arity () == 2) && isOpX<IMPL> (f)));
        Expr body = f->left ();
        ClpRule r (f->right ());      

        // Normalization of the body
        Expr nBody = op::boolop::gather (op::boolop::nnf (body));
        
        if (nBody->arity () == 1)
        { r.addBodyLiteral (nBody); }
        else if (nBody->arity () == 2)
        {
          if (isOpX<AND> (nBody))
          { 
            r.addBodyLiteral (nBody->left ());
            r.addBodyLiteral (nBody->right ());
          }
          else
            cout << "Warning: hornClp ignoring body" << *nBody << "\n";
        }
        else if (nBody->arity () >= 3)
        {
          if (isOpX<AND> (nBody))
          {
            for (ENode::args_iterator it = nBody->args_begin(), et = nBody->args_end();
                 it != et; ++it)
            { r.addBodyLiteral (*it); }
          }
          else
            cout << "Warning: hornClp ignoring body" << *nBody << "\n";
        }

        m_rules.push_back (r);
      }
    }
  }

  string ClpHornify::toString () const
  {
    std::ostringstream oss;
    for (auto &rule : m_rules)
    { oss  << rule; }

    oss << "false :- " << *m_query << ".\n";

    return oss.str ();
  }
}
