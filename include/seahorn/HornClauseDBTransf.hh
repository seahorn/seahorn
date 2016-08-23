#ifndef _HORN_CLAUSE_DB_TRANSFORMATIONS__H_
#define _HORN_CLAUSE_DB_TRANSFORMATIONS__H_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

namespace seahorn
{

  // Ensure all horn clause heads have only variables
  void normalizeHornClauseHeads (HornClauseDB &db);
  // Perform predicate abstraction to the Horn database
  void predicateAbstration (HornifyModule &hm);
}


#endif /* _HORN_CLAUSE_DB_TRANSFORMATIONS__H_ */
