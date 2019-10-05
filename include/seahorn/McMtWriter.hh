#ifndef _MCMT_WRITER__H_
#define _MCMT_WRITER__H_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

#include "seahorn/config.h"

namespace seahorn
{
  template <typename Out>
  class McMtWriter
  {
    HornClauseDB &m_db;
    ExprFactory &m_efac;
    EZ3 &m_z3;
    
    Expr trueE;
    
  public:
    McMtWriter (HornClauseDB &db, EZ3 &z3) :
      m_db (db), m_efac(db.getExprFactory ()), m_z3(z3)
    {trueE = mk<TRUE> (m_efac);} 
    
    Out &write (Out &out);
  };

  template <typename Out>
  Out &McMtWriter<Out>::write (Out &out)
  {

    // XXX We assume that the CHC follow the specific flarge encoding.
    if (!m_db.hasQuery ()) return out;

    
    auto &vars = m_db.getVars ();
    Expr query = m_db.getQueries ()[0];
    Expr tr = bind::fname (query);
    Expr errLoc = query->arg (1);
    
   
    out << ";; SeaHorn v." << SEAHORN_VERSION_INFO << "\n";
    out << "(define-state-type st_ty\n";
    
    out << "  (";
    for (unsigned i=0,sz=bind::domainSz (tr); i < sz; ++i)
    {
      Expr ty = bind::domainTy (tr, i);
      out << "(s" << i << " ";
      if (isOpX<BOOL_TY> (ty)) out << "Bool";
      else if (isOpX<REAL_TY> (ty)) out << "Real";
      else if (isOpX<INT_TY> (ty)) out << "Int";
      else
      {
        errs () << "Unsupported type: " << "s" << i << " type " << *ty << "\n";
        assert (false);
        return out;
      }
      out << ") ";
    }
    out << ")\n";
    

    // -- inputs
    out << "  (";
    for (auto v : vars)
    {
      out << "(" << m_z3.toSmtLib (v) << " ";
      
      Expr ty = bind::typeOf (v);
      if (isOpX<BOOL_TY> (ty)) out << "Bool";
      else if (isOpX<REAL_TY> (ty)) out << "Real";
      else if (isOpX<INT_TY> (ty)) out << "Int";
      else
      {
        errs () << "Unsupported type: " << m_z3.toSmtLib (v) << " type " << *ty << "\n";
        assert (false);
        return out;
      }
      out << ") ";
    }
    out << ")\n";
    
    out << ")\n";

    // -- initial state is pc=0
    out << "(define-states init st_ty (= s0 0))\n";

    unsigned c = 0;
    for (auto &r : m_db.getRules ())
    {
      // -- skip rules that do not define the main transition relation
      if (bind::fname (r.head ()) != tr) continue;
      // -- skip facts, we assume everything starts at pc=0
      if (isOpX<TRUE> (r.body ())) continue;
      
      ExprVector body;
      assert (isOpX<AND> (r.body ()));
      for (unsigned i=1,sz=r.body ()->arity (); i < sz; ++i)
        body.push_back (r.body ()->arg (i));
      
      out << "(define-transition " << *bind::fname (tr) << "_tr_" << c++
          << " st_ty\n";

      out << "(and \n";

      // -- prev state
      Expr st = r.body ()->arg (0);
      out << "  ";
      for (unsigned i=1, sz=st->arity (); i < sz; ++i)
        out << "(= state.s" << (i-1) << " " << *st->arg(i) << ") ";
      out << "\n";
      
      // -- next state
      out << "  ";
      for (unsigned i=1, sz=r.head()->arity(); i < sz; ++i)
        out << "(= next.s" << (i-1) << " " << *r.head ()->arg (i) << ") ";
      out << "\n";
      
      Expr phi = mknary<AND> (trueE, body);
      phi = z3_simplify (m_z3, phi);
      out << "  " << m_z3.toSmtLib (phi) << ")\n";
      out << ")\n";
    }
    
    out << "(define-transition-system " << *bind::fname (tr)
        << " st_ty init \n";
    out << "(or ";
    for (unsigned i = 0; i < c; ++i)
      out << *bind::fname (tr) << "_tr_" << i << " ";
    out << "))\n";
    
    out << "(query " << *bind::fname (tr) << "  (< s0 "
        << m_z3.toSmtLib (errLoc) << "))\n";
    
    return out;
  }
  
}

#endif /* _MCMT_WRITER__H_ */
