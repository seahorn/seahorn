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
    const ExprVector &m_rels;

   public:
    
    ClpRule (Expr head, Expr constraints, ExprFactory &efac, const ExprVector &rels): 
        m_head (head), m_body (constraints), 
        m_efac (efac), m_rels (rels) { }

    ClpRule (Expr head, Expr body, Expr constraints, ExprFactory &efac, const ExprVector &rels): 
        m_head (head), m_body (mk<AND> (body, constraints)), 
        m_efac (efac), m_rels (rels) { }
    
    void addBody (Expr body) { m_body = body; }
    
    bool isFact () const { return !m_body; }
      
    void normalize ();

    void print (ostream &o) const;
  };

  class ClpHornify 
  {
    const ExprVector &m_rels;
    vector<ClpRule> m_rules;
    ExprFactory &m_efac;

   public:

    ClpHornify (HornClauseDB &db, ExprFactory &efac);

    string toString () const;
  };
}

#endif 

