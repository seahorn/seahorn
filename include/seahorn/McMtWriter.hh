#ifndef _MCMT_WRITER__H_
#define _MCMT_WRITER__H_

#include "seahorn/HornClauseDB.hh"
#include "ufo/Expr.hpp"

namespace seahorn
{
  template <typename Out>
  class McMtWriter
  {
    HornClauseDB &m_db;
    ExprFactory &m_efac;
    
  public:
    McMtWriter (HornClauseDB &db) : m_db (db), m_efac(db.getExprFactory ()) {} ;
    Out &write (Out &out);
  };

  template <typename Out>
  Out &McMtWriter<Out>::write (Out &out)
  {
    return out;
  }
  
}

#endif /* _MCMT_WRITER__H_ */
