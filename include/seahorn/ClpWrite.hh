#ifndef _HORN_CLP_WRITE__HH_
#define _HORN_CLP_WRITE__HH_

#include <vector>
#include "seahorn/HornClauseDB.hh"
#include "seahorn/Expr/Expr.hh"

namespace seahorn
{
  using namespace std;
  using namespace llvm;

  class ClpWrite 
  {
   public:

    class ClpRule
    {
      Expr m_head;
      Expr m_body;
      ExprFactory &m_efac;
      const HornClauseDB::expr_set_type &m_rels;
      
     public:
      
      ClpRule (Expr head, Expr constraints, ExprFactory &efac,
               const HornClauseDB::expr_set_type &rels): 
          m_head (head), m_body (constraints), 
          m_efac (efac), m_rels (rels) { }
      
      ClpRule (Expr head, Expr body, Expr constraints, ExprFactory &efac,
               const HornClauseDB::expr_set_type &rels): 
          m_head (head), m_body (mk<AND> (body, constraints)), 
          m_efac (efac), m_rels (rels) { }
      
      void addBody (Expr body) { m_body = body; }
      
      bool isFact () const { return !m_body; }
      
      void normalize ();
      
      void print (ostream &o) const;
    };
    
   private:

    const HornClauseDB::expr_set_type &m_rels;
    vector<ClpRule> m_rules;
    ExprFactory &m_efac;

   public:

    ClpWrite (HornClauseDB &db, ExprFactory &efac);

    string toString () const;
  };
}

#endif 

