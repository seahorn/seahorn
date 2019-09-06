/* Slice the program on to a set of selected functions by command line */

#include "llvm/ADT/SCCIterator.h"
//#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "seahorn/Support/SeaDebug.h"

#include <set>
#include <vector>
//#include <iostream>
#include <fstream>
#include <string>
#include <sstream>

static llvm::cl::list<std::string>
FuncNamesToKeep("slice-function",
                llvm::cl::desc("Slice program onto these functions"),
                llvm::cl::ZeroOrMore, llvm::cl::CommaSeparated);

namespace seahorn {

  using namespace llvm;


  class SliceFunctions : public ModulePass
  {
   public:

    static char ID;

    SliceFunctions (): ModulePass (ID) {}

    virtual bool runOnModule (Module &M) {

      if (M.empty ())
        return false;

      if (FuncNamesToKeep.begin() == FuncNamesToKeep.end())
        return false;

      std::set<Function *> FuncsToKeep;
      for (std::string FuncName : FuncNamesToKeep) {
        Function *Func = M.getFunction(FuncName);
        if (!Func) {
          LOG ("slice",
               errs() << "SliceFunctions: " << FuncName <<  " not found.\n");
               printFunctionsInfo(M);
        } else {
          FuncsToKeep.insert(Func);
        }
      }

      // -- assume that we slice at least onto one function otherwise
      //    the module will be empty.
      if (FuncsToKeep.empty ())
        return false;

      bool Change = false;

      // --- Delete function bodies and set external linkage
      for (Function &F : M) {
        if (F.isDeclaration()) continue;
        if (FuncsToKeep.count(&F) > 0) continue;
        LOG ("slice",
             errs () << "SliceFunctions: deleted body of " << F.getName () <<"\n");
        F.deleteBody();
        F.setComdat(nullptr);
        Change = true;
      }
      
      // Delete global aliases
      // Aliases cannot point to a function declaration so if there is
      // an alias to a removed function we also need to remove all its
      // aliases.
      std::vector<GlobalAlias *> aliases;
      for (GlobalAlias &GA : M.aliases()) {
        aliases.push_back(&GA);
      }
      
      for (GlobalAlias *GA : aliases) {
        if (Function *aliasee = dyn_cast<Function>(GA->getAliasee())) {
          if (!(FuncsToKeep.count(aliasee) > 0)) {
            LOG ("slice", errs () << "SliceFunctions: removed alias " << *GA << "\n");
            GA->replaceAllUsesWith(aliasee);
	    GA->eraseFromParent();
            Change = true;
          }
        }
      }
      
      // If main is removed then CreateDummyMain pass must be run
      // otherwise the whole module will be empty.
      if (Function *Main = M.getFunction("main")) {
        if (FuncsToKeep.count (Main) <= 0) {
          LOG ("slice", errs () << "SliceFunctions: deleted main.\n");
          Main->dropAllReferences();
          Main->eraseFromParent();
          Change = true;
        }
      }
      return Change;
    }

    virtual void getAnalysisUsage (AnalysisUsage &AU){
      AU.setPreservesAll();
      //AU.addRequired<llvm::CallGraphWrapperPass>();
    }

    virtual StringRef getPassName () const override
    {return "SliceFunctions";}

   private:
     void printFunctionsInfo(Module &M) {
       std::stringstream info;
       info << "\t NUM_FUNCS: " << std::to_string(std::distance(M.begin(), M.end())) << ",\n";
       for (auto &F : M) {
	 unsigned numInsts = std::distance(inst_begin(&F), inst_end(&F));
	 std::string fn = F.getName();
	 errs() << "INC | " << F.getName()
		<< " | " << std::distance(F.begin(), F.end())
		<< " | " << numInsts << "\n";
	 info << "\t" << fn
	      << ":{ BLOCKS: " << std::to_string(std::distance(F.begin(), F.end()))
	      << ", INST: " << std::to_string(numInsts) + "},\n";
       }
     }

    // void printFunctionsInfo (Module& M) {
    //   CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
    //   CallGraph *CG = cgwp ? &cgwp->getCallGraph() : nullptr;

    //   if (CG) {
    //     // errs () << "==== Recursive functions ==== \n";
    //     // bool has_rec_func = false;
    //     // for (auto it = scc_begin (CG); !it.isAtEnd (); ++it) {
    //     //   auto &scc = *it;
    //     //   if (std::distance (scc.begin (), scc.end ()) > 1) {
    //     //     has_rec_func = true;
    //     //     errs () << "SCC={";
    //     //     for (CallGraphNode *cgn : scc) {
    //     //       if (cgn->getFunction ())
    //     //         errs () << cgn->getFunction ()->getName () << ";";
    //     //     }
    //     //   }
    //     // }
    //     // if (!has_rec_func) errs () << "None\n";
        
    //     typedef std::pair<Function *, std::pair<unsigned, unsigned>> func_ty;
    //     std::vector<func_ty> funcs;
    //     errs() << "=== Call graph and function information === \n";
    //     errs() << "TOTAL NUM of FUNCTIONS=" << std::distance(M.begin(), M.end())
    //            << "\n";
    //     for (auto it = scc_begin(CG); !it.isAtEnd(); ++it) {
    //       auto &scc = *it;
    //       for (CallGraphNode *cgn : scc) {
    //         if (cgn->getFunction() && !cgn->getFunction()->isDeclaration()) {
    //           funcs.push_back(std::make_pair(
    //               cgn->getFunction(),
    //               std::make_pair(cgn->getNumReferences(),
    //                              std::distance(cgn->begin(), cgn->end()))));
    //         }
    //       }
    //     }
        
    //     std::sort(funcs.begin(), funcs.end(), [](func_ty p1, func_ty p2) {
    //         return (p1.second.first + p1.second.second) >
    //             (p2.second.first + p2.second.second);
    //       });
        
    //     for (auto &p : funcs) {
    //       Function *F = p.first;
    //       unsigned numInsts = std::distance(inst_begin(F), inst_end(F));
    //       errs() << F->getName() << " --- NUM INST=" << numInsts
    //              << " CALLERS=" << p.second.first << " CALLEES=" << p.second.second
    //              << "\n";
    //     }
    //   } else {
    //     // errs () << "Call graph not found.\n";
    //     errs() << "=== Function information === \n";
    //     errs() << "TOTAL NUM of FUNCTIONS=" << std::distance(M.begin(), M.end())
    //            << "\n";
    //     for (auto &F : M) {
    //       unsigned numInsts = std::distance(inst_begin(&F), inst_end(&F));
    //       errs() << F.getName()
    //              << "--- NUM BLOCKS=" << std::distance(F.begin(), F.end())
    //              << " NUM INST=" << numInsts << "\n";
    //     }
    //   }
    // }

  };

  char SliceFunctions::ID = 0;

  Pass* createSliceFunctionsPass () {
    return new SliceFunctions ();
  }

} // end namespace
