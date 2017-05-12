/* Externalize functions selected by command line */

#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/Debug.h"

#include "avy/AvyDebug.h"

#include <regex>
#include "boost/optional.hpp"

using namespace llvm;

#define EXTERN_FUNCTIONS_USE_REGEX

static llvm::cl::list<std::string>
ExternalizeFunctionNames("externalize-function",
                         llvm::cl::desc("Set the linkage to external"),
                         llvm::cl::ZeroOrMore);

namespace seahorn
{

  class ExternalizeFunctions : public ModulePass
  {

    #ifdef EXTERN_FUNCTIONS_USE_REGEX
    struct MatchRegex : public std::unary_function<Function*, bool> {
      boost::optional <std::regex> m_re;
      MatchRegex (std::string s) { 
        if (s != "") {
          try { m_re = std::regex (s);  }  
          catch (std::regex_error& e) 
          {
            errs () << "Warning: syntax error in the regex: " << e.what () << "\n";
          }
        }
      }
      bool operator() (Function* F)  {
        if (!m_re) return false;  // this should not happen
        return std::regex_match (F->getName ().str(), *m_re);
      }
    };
    #endif 

   public:
    
    static char ID;
    
    ExternalizeFunctions (): ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M) {

      if (ExternalizeFunctionNames.begin() == ExternalizeFunctionNames.end())
        return false;
      
      SmallPtrSet<Function*, 16> externalizeFunctions;
      for (auto name : ExternalizeFunctionNames) {
        #ifndef EXTERN_FUNCTIONS_USE_REGEX
        if (Function *F = M.getFunction(name))
          externalizeFunctions.insert (F);
        #else
        MatchRegex filter (name);
        for (auto& F: M) {
          if (filter (&F)) {
            externalizeFunctions.insert (&F);
          }
        }
        #endif 
      }


      bool Change = false;
      // Delete function bodies and set external linkage
      for (Function &F : M) {
        if (F.isDeclaration() || !(externalizeFunctions.count(&F) > 0)) 
          continue;
        LOG("extern", 
            errs () << "EXTERNALIZED " << F.getName () << "\n");
        F.deleteBody();
        Change = true;
      }

      // Delete global aliases: aliases cannot point to a function
      // declaration so if there is an alias to an external function
      // we also need to remove all its aliases.
      std::vector<GlobalAlias *> aliases;
      for (GlobalAlias &GA : M.aliases()) {
        aliases.push_back(&GA);
      }

      for (GlobalAlias *GA : aliases) {
        if (Function *aliasee = dyn_cast<Function>(GA->getAliasee())) {
          if (externalizeFunctions.count(aliasee) > 0) {
            GA->replaceAllUsesWith(aliasee);
            M.getAliasList().erase(GA);
            Change = true;
          }
        }
      }

      return Change;
    }
    
    void getAnalysisUsage (AnalysisUsage &AU) {
      AU.setPreservesAll ();
    }

    virtual const char* getPassName () const 
    {return "Externalize all selected functions";}
    
  };

   char ExternalizeFunctions::ID = 0;

   Pass* createExternalizeFunctionsPass () {
     return new ExternalizeFunctions ();
   }
   
} // end namespace   
      


