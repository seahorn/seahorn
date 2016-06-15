#include "seahorn/Houdini.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

namespace seahorn
{
  char Houdini::ID = 0;
  bool Houdini::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    //load the Horn clause database
    auto &db = hm.getHornClauseDB ();

    //print hello
    printHello();
  }

  void Houdini::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  void Houdini::printDB (const HornClauseDB &db)
  {
    outs () << db << "\n";
  }

  void Houdini::printHello ()
  {
    outs () << "Hello there.\n";
  }
}
