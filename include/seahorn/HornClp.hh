#ifndef _HORN_CLP__HH_
#define _HORN_CLP__HH_

#include <vector>
#include "seahorn/HornClauseDB.hh"
#include "ufo/Expr.hpp"
#include <llvm/Support/raw_ostream.h>

namespace seahorn
{
  using namespace std;
  using namespace llvm;

  class ClpHornify 
  {
    class ClpRule
    {
      Expr m_head;
      vector<Expr> m_body;

     public:

      ClpRule (Expr head): m_head (head) { }
      
      void addLiteral (Expr lit) { m_body.push_back (lit); }

      bool isFact () const { return m_body.empty (); }
      
      void write (ostream &o) const
      {        
        if (isFact())
        { o << *m_head << "."; }
        else
        {
          o << *m_head << " :- ";
          for (auto const &e : m_body)
          { o << "\n\t" << *e << ","; }
          o << ".";
        }
      }

      friend ostream& operator<< (ostream &o, const ClpRule &r) 
      {
        r.write (o);
        return o;
      }
    };

    raw_ostream& m_os;
    Expr m_query;
    vector<ClpRule> m_rules;

   public:

    ClpHornify (HornClauseDB &db, raw_ostream &OS);

    // In the future, we might want to support different CLP
    // dialects. In that case, ClpHornify can have the method dump as
    // virtual.
    void write () const;

  };
}

#endif 

