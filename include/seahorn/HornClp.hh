#ifndef _HORN_CLP__HH_
#define _HORN_CLP__HH_

#include <vector>
#include "seahorn/HornClauseDB.hh"
#include "ufo/Expr.hpp"

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
      
      void addBodyLiteral (Expr lit) { m_body.push_back (lit); }

      bool isFact () const { return m_body.empty (); }
      
      void write (ostream &o) const
      {        
        assert (m_head);

        if (isFact())
        { o << *m_head << ".\n"; }
        else
        {
          o << *m_head << " :- ";
          for (auto it = m_body.begin (), et = m_body.end (); it!=et;  )
          {
            Expr e = *it;
            o << "\n\t" << *e;
            ++it;
            if (it != et)
              o << ","; 
          }
          o << ".\n";
        }
      }

      friend ostream& operator<< (ostream &o, const ClpRule &r) 
      {
        r.write (o);
        return o;
      }
    };

    Expr m_query;
    vector<ClpRule> m_rules;

   public:

    ClpHornify (HornClauseDB &db);

    string toString () const;

  };
}

#endif 

