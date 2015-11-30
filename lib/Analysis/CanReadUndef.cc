#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/PassManager.h"

#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfo.h"

#include "llvm/Support/CommandLine.h"

using namespace llvm;

static llvm::cl::opt<bool>
UndefWarningErr ("horn-make-undef-warning-error", 
                 llvm::cl::desc ("Make warnings of undefined reads into errors"),
                 llvm::cl::init (true));

namespace seahorn {
  
   class CanReadUndef : public ModulePass {

     static bool printDebugLoc (const Instruction *inst)
     {
       if (!inst) return false;

       const DebugLoc &dloc = inst->getDebugLoc ();

       if (dloc.isUnknown ()) return false;

       unsigned Line = dloc.getLine ();
       unsigned Col = dloc.getCol ();
       std::string File; 
       DIScope Scope (dloc.getScope ());
       if (Scope) File = Scope.getFilename ();
       else File = "unknown file";

       errs () << "--- File: " << File << "\n"
               << "--- Line: " << Line  << "\n" 
               << "--- Column: " << Col << "\n";
               
       return true;
     }


     bool m_undef_found;

   public:
    
    static char ID;

    CanReadUndef() : ModulePass(ID), m_undef_found (false) { }
    
    virtual bool runOnModule(Module &M)  {
      
      bool Changed = false;
      
      //Iterate over all functions, basic blocks and instructions.
      for (Module::iterator FI = M.begin(), E = M.end(); FI != E; ++FI)
        Changed |= runOnFunction (*FI);


      if (UndefWarningErr && m_undef_found) {
        // aborting ...
        exit (1);
      }
      
      return Changed;
    }
    
    bool runOnFunction (Function &F) {

      for (BasicBlock &b : F)
        // -- go through all the reads
        for (User &u : b)
        {
          // phi-node
          if (PHINode* phi = dyn_cast<PHINode> (&u))
          {
            for (unsigned i = 0; i < phi->getNumIncomingValues (); i++)
            {
              if (isa<UndefValue> (phi->getIncomingValue (i)))
              {
                if (errs().has_colors()) errs().changeColor(UndefWarningErr ? 
                                                            raw_ostream::RED : 
                                                            raw_ostream::YELLOW);

                if (UndefWarningErr) errs () << "ERROR: ";
                else errs () << "Warning: ";

                errs () << "read of an undefined value.\n";
                
                if (!UndefWarningErr) {
                  errs () << "This normally indicates that the program should be fixed, "
                          << "otherwise SeaHorn will probably crash.\n";
                }

                if (errs().has_colors()) errs().resetColor();

                if (!printDebugLoc (dyn_cast<Instruction> (phi)))
                  errs () << "No location found. Make sure you run with -g flag.\n";
                
                errs () << "\n";

                m_undef_found = true;
              }
              
            }
            
            continue;
          }
          
          // -- the normal case
          for (unsigned i = 0; i < u.getNumOperands (); i++)
          {
            if (isa <UndefValue> (u.getOperand (i)))
            {
                if (errs().has_colors()) errs().changeColor(UndefWarningErr ? 
                                                            raw_ostream::RED : 
                                                            raw_ostream::YELLOW);

                if (UndefWarningErr) errs () << "ERROR: ";
                else errs () << "Warning: ";

                errs () << "read of an undefined value.\n";

                if (!UndefWarningErr)
                  errs () << "This normally indicates that the program should be fixed, "
                          << "otherwise SeaHorn will probably crash.\n";
                
                if (errs().has_colors()) errs().resetColor();
                
                if (!printDebugLoc (dyn_cast<Instruction> (u.getOperand (i))))
                  errs () << "No location found. Make sure you run with -g flag.\n";
                
              errs () << "\n";

              m_undef_found = true;
            }
          }
        }
      return false;
    }
    

    virtual void getAnalysisUsage (AnalysisUsage &AU) const  {
      AU.setPreservesAll ();
    }
    
  };
  
  char CanReadUndef::ID = 0;

  llvm::Pass* createCanReadUndefPass () {return new CanReadUndef ();}

}

static RegisterPass<seahorn::CanReadUndef> 
X ("read-undef", 
   "Verify if an undefined value can be read", 
   false, 
   false);
