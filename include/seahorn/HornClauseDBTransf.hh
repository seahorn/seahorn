// Horn Clause DB Transformations
#pragma once

#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/HornClauseDB.hh"

namespace seahorn {

// Ensure all horn clause heads have only variables
void normalizeHornClauseHeads(HornClauseDB &db);

// \brief rewrites the horn clauses to remove finite map terms (new relations
// are created for the relations that contain finite maps as arguments)
void removeFiniteMapsHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb);

// \brief rewrites the bodies of the horn clauses to remove finite map
// primitives `zctx` is used to simplify
void removeFiniteMapsBodyHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb,
                                           EZ3 &zctx);
} // namespace seahorn
