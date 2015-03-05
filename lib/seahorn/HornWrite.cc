#include "seahorn/HornWrite.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClp.hh"

#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<bool>
InternalWriter("horn-fp-internal-writer",
               llvm::cl::desc("Use internal writer for Horn SMT2 format. (Default)"),
               llvm::cl::init(true),llvm::cl::Hidden);

enum HCFormat { SMT2, CLP};
static llvm::cl::opt<HCFormat>
HornClauseFormat("horn-format",
       llvm::cl::desc ("Specify the format for Horn Clauses"),
       llvm::cl::values 
       (clEnumValN (SMT2,"smt2",
                    "SMT2 (default)"),
        clEnumValN (CLP, "clp",
                    "CLP (Constraint Logic Programming)"),
        clEnumValEnd),
       llvm::cl::init (SMT2));

namespace seahorn
{
  char HornWrite::ID = 0;
  
  void HornWrite::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll ();
  }
  
  bool HornWrite::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    HornClauseDB &db = hm.getHornClauseDB ();
    if (HornClauseFormat == CLP)
    {
      ClpHornify writer (db);
      m_out << writer.toString ();
    }
    else 
    {
      // FIXME: when HornWrite is called hm.getZFixedPoint () is still
      // empty because the content of HornClauseDB is not loaded until
      // HornSolver is called.
      ZFixedPoint<EZ3> fp (hm.getZContext ());
      {
        for (auto &p: db.getRelations ())
        { 
          fp.registerRelation (p); 
          fp.addCover (p, db.getConstraints (p)); 
        }
        for (auto &r: db.getRules ())
        { fp.addRule (r.vars (), r.body ()); }
        fp.addQuery (db.getQuery ());
      }

      if (InternalWriter)
        m_out << fp /*hm.getZFixedPoint ()*/ << "\n";
      else
        m_out << fp.toString () /*hm.getZFixedPoint ().toString ()*/ << "\n";
    }
    
    m_out.flush ();
    return false;
  }
  
}
