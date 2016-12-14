#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/PassManager.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfo.h"

#include "llvm/Support/CommandLine.h"

using namespace llvm;

static llvm::cl::opt<bool>
ReportError ("horn-make-undef-warning-error", 
             llvm::cl::desc ("Make warnings of undefined reads into errors"),
             llvm::cl::init (false));

namespace seahorn {
  
   class CanReadUndef : public ModulePass {

     static bool hasDebugLoc (const Instruction *inst) {
       if (!inst) return false;

       const DebugLoc &dloc = inst->getDebugLoc ();

       return (!(dloc.isUnknown ()));
     }

     static void printDebugLoc (const Instruction *inst, llvm::raw_ostream& os) {

       assert (hasDebugLoc(inst));

       const DebugLoc &dloc = inst->getDebugLoc ();
       unsigned Line = dloc.getLine ();
       unsigned Col = dloc.getCol ();
       std::string File; 
       DIScope Scope (dloc.getScope ());
       if (Scope) File = Scope.getFilename ();
       else File = "unknown file";

       os << "Possible read of undefined value at \n"
          << "--- File   : " << File << "\n"
          << "--- Line   : " << Line << "\n" 
          << "--- Column : " << Col  << "\n"
	  << "--- Bitcode: " << *inst << "\n";
     }

     unsigned m_undef_num;
     std::string m_msg;

   public:
    
     static char ID;
     
     CanReadUndef() : ModulePass(ID), m_undef_num(0), m_msg("") { }
    
     virtual bool runOnModule(Module &M)  {
       
       bool Changed = false;
       
       //Iterate over all functions, basic blocks and instructions.
       for (Module::iterator FI = M.begin(), E = M.end(); FI != E; ++FI)
         Changed |= runOnFunction (*FI);
       
       if (m_undef_num > 0) {
         
         if (errs().has_colors()) errs().changeColor(ReportError ? 
                                                     raw_ostream::RED : 
                                                     raw_ostream::YELLOW);
         if (ReportError) 
           errs () << "Error: ";
         else 
           errs () << "Warning: ";
         
         errs () << "found " << m_undef_num << " possible reads of undefined values\n";
         
         if (m_msg != "") errs () << m_msg;
           
         if (errs().has_colors()) errs().resetColor();
         
         if (ReportError)
           llvm::report_fatal_error("Aborting ...");
       }
       
      return Changed;
     }
    
    bool runOnFunction (Function &F) {

      for (BasicBlock &b : F)
        // -- go through all the reads
        for (User &u : b) {
          // phi-node
          if (PHINode* phi = dyn_cast<PHINode> (&u)) {
            for (unsigned i = 0; i < phi->getNumIncomingValues (); i++) {
              if (isa<UndefValue> (phi->getIncomingValue (i))) {
                m_undef_num++;
                if (hasDebugLoc (dyn_cast<Instruction>(&u))) {		
                  raw_string_ostream os(m_msg);
		  printDebugLoc(dyn_cast<Instruction>(&u), os);
                }
              }
            }
            continue;
          }
          
          // -- the normal case
          for (unsigned i = 0; i < u.getNumOperands (); i++) {
            if (isa <UndefValue> (u.getOperand (i))) {
              m_undef_num++;
	      if (hasDebugLoc(dyn_cast<Instruction>(&u))) {
                raw_string_ostream os(m_msg);
		printDebugLoc(dyn_cast<Instruction>(&u), os);		
              }
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
X ("read-undef", "Verify if an undefined value can be read", false, false);
   
