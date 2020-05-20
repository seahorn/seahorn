// Horn Clause DB Transformations
#pragma once

#include "seahorn/HornClauseDB.hh"

namespace seahorn
{

// Ensure all horn clause heads have only variables
void normalizeHornClauseHeads (HornClauseDB &db);

// Remove arguments of type FiniteMap from Horn Clauses
void removeFiniteMapsArgsHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb);

// Remove expressions of type FiniteMap from the horn clause bodies, excluding
// calls to predicates
void removeFiniteMapsBodiesHornClausesTransf(HornClauseDB & db);

}
