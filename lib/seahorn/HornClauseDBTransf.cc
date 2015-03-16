#include "seahorn/HornClauseDBTransf.hh"
#include "ufo/Expr.hpp"

namespace seahorn
{
  using namespace expr;
  using namespace std;
  
  // Ensure that all HC heads have only variables
  void replaceNonVarsInHead (HornRule &r) 
  {
    Expr h = r.head ();
    assert (bind::isFapp (h));
    ExprFactory& efac = h->efac ();

    ENode::args_iterator it = ++ (h->args_begin ());
    ENode::args_iterator end = h->args_end ();
    Expr new_body = mk<TRUE> (efac);
    ExprVector new_args;
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
      }
      else 
      { new_args.push_back (arg); }
    }

    r.setHead (bind::fapp (*(h->args_begin()), new_args));
    r.setBody (boolop::land (new_body, r.body ()));
  }


  void normalizeHornClauseHeads (HornClauseDB &db)
  {
    for (auto &r: db.getRules ())
    { replaceNonVarsInHead (r); }
  }
}
