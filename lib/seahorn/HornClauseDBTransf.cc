#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/PredicateAbstraction.hh"
#include "seahorn/HornifyModule.hh"
#include "ufo/Expr.hpp"

namespace seahorn
{
  using namespace expr;
  using namespace std;
  
  // Return a new Horn rule whose head only has variables
  HornRule replaceNonVarsInHead (const HornRule &rule) 
  {
    Expr h = rule.head ();
    assert (bind::isFapp (h));
    ExprFactory& efac = h->efac ();

    ENode::args_iterator it = ++ (h->args_begin ());
    ENode::args_iterator end = h->args_end ();
    Expr new_body = mk<TRUE> (efac);
    ExprVector new_args, new_vars;
    unsigned int id = 0;
    for (; it != end; ++it)
    {
      Expr arg = *it;
      if (isOpX<GT> (arg) || isOpX<GEQ> (arg) || isOpX<LT> (arg) || 
          isOpX<LEQ> (arg) || isOpX<EQ> (arg) || isOpX<NEQ> (arg) )
      {
        std::string vname("VAR_");
        vname += boost::lexical_cast<string> (++id);
        Expr v = bind::intConst (mkTerm<std::string> (vname, efac));
        new_body = boolop::land (new_body, 
                                 mk<OR>(mk<AND>(mk<EQ> (v, mkTerm (mpz_class(1), efac)), arg),
                                        mk<AND>(mk<EQ> (v, mkTerm (mpz_class(0), efac)), mk<NEG> (arg))));
        new_args.push_back (v);
        new_vars.push_back (v);
      }
      else if (isOpX<PLUS>(arg) || isOpX<MINUS>(arg) || 
               isOpX<MULT>(arg) || isOpX<DIV>(arg) || 
               isOpX<MPQ> (arg) || isOpX<MPZ> (arg))
      {
        std::string vname("VAR_");
        vname += boost::lexical_cast<string> (++id);
        Expr v = bind::intConst (mkTerm<std::string> (vname, efac));
        new_body = boolop::land (new_body, mk<EQ> (v, arg));
        new_args.push_back (v);
        new_vars.push_back (v);
      }
      else 
      { new_args.push_back (arg); }
    }
    Expr head = bind::fapp (*(h->args_begin()), new_args);
    Expr body = boolop::land (new_body, rule.body ());

    boost::copy (rule.vars (), std::back_inserter (new_vars));
    HornRule new_rule (new_vars, head, body);
    return new_rule;
  }


  void normalizeHornClauseHeads (HornClauseDB &db)
  {
    vector<HornRule> worklist;
    boost::copy (db.getRules (), std::back_inserter(worklist));

    for (auto rule: worklist)
    {
      HornRule new_rule = replaceNonVarsInHead (rule);        
      db.removeRule (rule);
      db.addRule (new_rule);
    }
  }
}
