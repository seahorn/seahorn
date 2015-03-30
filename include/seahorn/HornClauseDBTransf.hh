#ifndef _HORN_CLAUSE_DB_TRANSFORMATIONS__H_
#define _HORN_CLAUSE_DB_TRANSFORMATIONS__H_

#include "seahorn/HornClauseDB.hh"

namespace seahorn
{

  // Ensure all horn clause heads have only variables
  void normalizeHornClauseHeads (HornClauseDB &db);

}


#endif /* _HORN_CLAUSE_DB_TRANSFORMATIONS__H_ */
