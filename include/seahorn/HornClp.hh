#ifndef _HORN_CLP__HH_
#define _HORN_CLP__HH_

#include <vector>
#include "seahorn/HornClauseDB.hh"
#include "ufo/Expr.hpp"

namespace seahorn
{
  using namespace std;
  using namespace llvm;

  class ClpRule
  {
    Expr m_head;
    Expr m_body;
    ExprFactory &m_efac;
    
   public:
    
    ClpRule (Expr head, ExprFactory &efac): 
        m_head (head), m_efac (efac) { }

    ClpRule (Expr head, Expr body, ExprFactory &efac): 
        m_head (head), m_body (body), m_efac (efac) { }
    
    void addBody (Expr body) { m_body = body; }
    
    bool isFact () const { return !m_body; }
      
    void normalize ();

    void print (ostream &o) const;
  };

  class ClpHornify 
  {
    Expr m_query;
    vector<ClpRule> m_rules;
    ExprFactory &m_efac;

   public:

    ClpHornify (HornClauseDB &db, ExprFactory &efac);

    string toString () const;
  };
}

#endif 

