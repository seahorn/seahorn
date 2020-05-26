// Horn Clause DB Transformations
#pragma once

#include "seahorn/HornClauseDB.hh"

namespace seahorn {

// Ensure all horn clause heads have only variables
void normalizeHornClauseHeads(HornClauseDB &db);

// Rewrites the Horn Clauses to remove Finite Map terms (new relations are
// created for the relations that contain Finite Maps as arguments)
void removeFiniteMapsHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb);

} // namespace seahorn
