/* 

   This pass aims at profiling the complexity of a program for the
   purpose of proving absence of certain kind of errors such as
   out-of-bound accesses, division by zero, use of uninitialized
   variables, etc.

*/

#include "llvm/Pass.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Format.h"
#include "llvm/Target/TargetLibraryInfo.h"

#include <boost/unordered_map.hpp>

using namespace llvm;

#include "llvm/IR/Instruction.def"

namespace seahorn {

  struct Counter {
    unsigned int Id;
    const char*Name;
    unsigned int Value;

    Counter (unsigned int id, const char *name): 
        Id (id), Name(name), Value(0) { }

    bool operator<(const Counter&o) const {
      if (int Cmp = std::strcmp(getName(), o.getName()))
        return Cmp < 0;
      // secondary key
      return Id < o.Id;
    }

    unsigned int getValue() const { return Value; }
    const char *getName() const { return Name; }
    void operator++() { Value++; }
    void operator+=(unsigned val) { Value += val; }
  };


  class CanReadUndef {
    
    static bool printDebugLoc (const Instruction *inst, std::string &msg) {
      if (!inst) return false;
      
      const DebugLoc &dloc = inst->getDebugLoc ();
      if (dloc.isUnknown ()) return false;

      unsigned Line = dloc.getLine ();
      unsigned Col = dloc.getCol ();
      std::string File; 
      DIScope Scope (dloc.getScope ());
      if (Scope) File = Scope.getFilename ();
      else File = "unknown file";
      
      msg += "--- File: " + File + "\n"
          + "--- Line: " + std::to_string(Line)  + "\n" 
          + "--- Column: " + std::to_string(Col) + "\n";
      
      return true;
    }
    
    
    bool runOnFunction (Function &F) {
      for (BasicBlock &b : F) {
        // -- go through all the reads
        for (User &u : b) {
          // phi-node
          if (PHINode* phi = dyn_cast<PHINode> (&u)) {
            for (unsigned i = 0; i < phi->getNumIncomingValues (); i++) {
              if (isa<UndefValue> (phi->getIncomingValue (i))) {
                printDebugLoc (dyn_cast<Instruction> (phi), report);
                num_undef++;
              }              
            }            
            continue;
          }
          // -- the normal case
          for (unsigned i = 0; i < u.getNumOperands (); i++) {
            if (isa <UndefValue> (u.getOperand (i))) {
              printDebugLoc (dyn_cast<Instruction> (u.getOperand (i)), report);
              num_undef++;
            }
          }
        }
      }
      return false;
    }
    
    unsigned int num_undef;
    std::string report;
    
   public:
    
    CanReadUndef(): num_undef (0) { }
    
    bool runOnModule(Module &M)  {
      for (Module::iterator FI = M.begin(), E = M.end(); FI != E; ++FI)
        runOnFunction (*FI);
      return false;
    }
    
    void printReport (raw_ostream &O) {
      O << " =========================== \n";
      O << "   Undefined value analysis  \n";
      O << " ============================\n";
      O << num_undef << " Number of possible uses of undefined values\n";
      O << report << "\n";
    }
  };

  class Profiler : public ModulePass, public InstVisitor<Profiler> {
    friend class InstVisitor<Profiler>;

    boost::unordered_map <unsigned int, Counter> counters;
    unsigned CounterId;

    void incrCounter (unsigned id, const char* name, unsigned val) {
      auto it = counters.find (id);
      if (it != counters.end ())
        it->second += val;
      else
        counters.insert (std::make_pair (id, Counter (id, name)));
    }

    Counter mkCounter (const char* name) {
      Counter res (CounterId++, name);
      return res;
    }

    void formatCounters (std::vector<Counter>& counters, 
                         unsigned& MaxNameLen, 
                         unsigned& MaxValLen,
                         bool sort = true) {
      // Figure out how long the biggest Value and Name fields are.
      for (auto c: counters) {
        MaxValLen = std::max(MaxValLen,
                             (unsigned)utostr(c.getValue()).size());
        MaxNameLen = std::max(MaxNameLen,
                              (unsigned)std::strlen(c.getName()));
      }

      if (sort) {
        // Sort the fields by name.
        std::stable_sort(counters.begin(), counters.end());
      }
    }

    const DataLayout* DL;
    TargetLibraryInfo* TLI;
    StringSet<> ExtFuncs;

    unsigned int TotalFuncs;
    unsigned int TotalBlocks;
    unsigned int TotalJoins;
    unsigned int TotalInsts;
    unsigned int TotalDirectCalls;
    unsigned int TotalIndirectCalls;
    unsigned int TotalExternalCalls;
    ///
    unsigned int SafeIntDiv;
    unsigned int SafeFPDiv;
    unsigned int UnsafeIntDiv;
    unsigned int UnsafeFPDiv;
    unsigned int DivIntUnknown;
    unsigned int DivFPUnknown;
    /// 
    unsigned int TotalMemAccess;
    unsigned int MemUnknown;
    unsigned int SafeMemAccess;
    ///
    unsigned int SafeLeftShift;
    unsigned int UnsafeLeftShift;
    unsigned int UnknownLeftShift;

    void visitFunction  (Function &F) { ++TotalFuncs; }
    void visitBasicBlock(BasicBlock &BB) { 
      ++TotalBlocks; 
      if (!BB.getSinglePredecessor ())
        ++TotalJoins;
    }

    void visitCallSite(CallSite &CS) {
      Function* callee = CS.getCalledFunction ();
      if (callee) {
        TotalDirectCalls++;
        if (callee->isDeclaration ()) {
          TotalExternalCalls++;
          ExtFuncs.insert (callee->getName ());
        }
      }
      else
        TotalIndirectCalls++;
    }

    void processPointerOperand (Value* V) {
      TotalMemAccess++;
      uint64_t Size;
      if (getObjectSize (V, Size, DL, TLI, true)) {
        SafeMemAccess++;
      } else {
        MemUnknown++;        
      }
    }

    void visitBinaryOperator (BinaryOperator* BI) {
      if (BI->getOpcode () == BinaryOperator::SDiv || 
          BI->getOpcode () == BinaryOperator::UDiv ||
          BI->getOpcode () == BinaryOperator::SRem ||
          BI->getOpcode () == BinaryOperator::URem ||
          BI->getOpcode () == BinaryOperator::FDiv || 
          BI->getOpcode () == BinaryOperator::FRem) {
        const Value* divisor = BI->getOperand (1);
        if (const ConstantInt *CI = dyn_cast<const ConstantInt> (divisor)) {
          if (CI->isZero ()) UnsafeIntDiv++;
          else SafeIntDiv++;
        }
        else if (const ConstantFP *CFP = dyn_cast<const ConstantFP> (divisor)) {
          if (CFP->isZero ()) UnsafeFPDiv++;
          else SafeFPDiv++;
        }
        else {
          // cannot figure out statically
          if (BI->getOpcode () == BinaryOperator::SDiv ||
              BI->getOpcode () == BinaryOperator::UDiv ||
              BI->getOpcode () == BinaryOperator::SRem ||
              BI->getOpcode () == BinaryOperator::URem)
            DivIntUnknown++;
          else 
            DivFPUnknown++;
        }
      }
      else if (BI->getOpcode () == BinaryOperator::Shl) {
        // Check for oversized shift amounts
        if (const ConstantInt *CI = dyn_cast<const ConstantInt> (BI->getOperand (1))) {
          APInt shift = CI->getValue ();
          if (CI->getType ()->isIntegerTy ()) {
            APInt bitwidth (32, CI->getType ()->getIntegerBitWidth (), true);
            if (shift.slt (bitwidth))
              SafeLeftShift++;
            else
              UnsafeLeftShift++;
          }
          else 
            UnknownLeftShift++;
        }
        else 
          UnknownLeftShift++;
      }
    }

    #define HANDLE_INST(N, OPCODE, CLASS)                    \
    void visit##OPCODE(CLASS &I) {                           \
      incrCounter (N, #OPCODE, 1);                           \
      ++TotalInsts;                                          \
      if (CallInst* CI = dyn_cast<CallInst>(&I)) {           \
         CallSite CS (CI);                                   \
         visitCallSite (CS);                                 \
      }                                                      \
      else if (InvokeInst* II = dyn_cast<InvokeInst>(&I)) {  \
         CallSite CS (II);                                   \
         visitCallSite (CS);                                 \
      }                                                      \
      else if (BinaryOperator* BI = dyn_cast<BinaryOperator>(&I)) { \
         visitBinaryOperator (BI);                                  \
      }                                                             \
      else if (isa<MemTransferInst>(&I)) {                          \
         TotalMemAccess++;                                          \
         MemUnknown++;                                              \
      }                                                             \
      else if (isa<MemSetInst>(&I)) {                               \
         TotalMemAccess++;                                          \
         MemUnknown++;                                              \
      }                                                             \
      else if (LoadInst* LI = dyn_cast<LoadInst>(&I)) {             \
         processPointerOperand (LI->getPointerOperand ());          \
      }                                                             \
      else if (StoreInst* SI = dyn_cast<StoreInst>(&I)) {           \
         processPointerOperand (SI->getPointerOperand ());          \
      }                                                             \
    }

    #include "llvm/IR/Instruction.def"

    void visitInstruction(Instruction &I) {
      errs() << "Instruction Count does not know about " << I;
      llvm_unreachable(nullptr);
    }

  public:

    static char ID; 

    Profiler() : 
        ModulePass(ID),
        CounterId (0),
        DL (nullptr), TLI (nullptr),
        TotalFuncs (0), TotalBlocks (0), TotalJoins (0), TotalInsts (0),
        TotalDirectCalls (0), TotalExternalCalls (0), TotalIndirectCalls (0),
        ////////
        SafeIntDiv (0), SafeFPDiv (0), 
        UnsafeIntDiv (0), UnsafeFPDiv (0), DivIntUnknown (0), DivFPUnknown (0),
        /////////
        TotalMemAccess (0), SafeMemAccess (0), MemUnknown (0),
        /////////
        SafeLeftShift (0), UnsafeLeftShift (0), UnknownLeftShift(0)
    { }

    bool runOnFunction(Function &F)  {
       visit(F);
       return false;
    }

    bool runOnModule (Module &M) override {

      DL = &getAnalysis<DataLayoutPass>().getDataLayout ();
      TLI = &getAnalysis<TargetLibraryInfo>();

      /// Look at the callgraph 
      // CallGraphWrapperPass *cgwp = &getAnalysis<CallGraphWrapperPass> ();
      // if (cgwp) {
      //   cgwp->print (errs (), &M);
      // }

      CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();

      typedef std::pair <Function*, std::pair <unsigned, unsigned> > func_ty;
      std::vector<func_ty> funcs;
    
      errs () << " ===================================== \n";
      errs () << "  Call graph information\n";
      errs () << " ===================================== \n";
      errs () << "Total number of functions=" << std::distance(M.begin(), M.end()) << "\n";
      for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it) {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc) {
          if (cgn->getFunction () && !cgn->getFunction ()->isDeclaration ()) {
             funcs.push_back (std::make_pair (cgn->getFunction (), 
                              std::make_pair (cgn->getNumReferences (), 
                                              std::distance (cgn->begin (), cgn->end ()))));
             // errs () << cgn->getFunction ()->getName () 
             //         << " callers=" << cgn->getNumReferences ()
             //         << " callees=" << std::distance (cgn->begin (), cgn->end ()) 
             //         << "\n";
          }
        }
      }

      bool has_rec_func = false;
      for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it) {
        auto &scc = *it;
        if (std::distance (scc.begin (), scc.end ()) > 1) {
           has_rec_func = true;
           errs () << "Found recursive SCC={";
           for (CallGraphNode *cgn : scc) {
             if (cgn->getFunction ())
                errs () << cgn->getFunction ()->getName () << ";";
           }
        }
      }
      if (!has_rec_func) 
         errs () << "No recursive functions found\n";


      std::sort (funcs.begin(), funcs.end (), 
                 [](func_ty p1, func_ty p2) { 
                     return   (p1.second.first + p1.second.second) > 
                              (p2.second.first + p2.second.second);
                 });

      for (auto&p: funcs){
          Function* F = p.first;
          unsigned numInsts = std::distance(inst_begin(F), inst_end(F));
          errs () << F->getName () << ":" 
                  << " num of instructions=" << numInsts
                  << " num of callers=" << p.second.first 
                  << " num of callees=" << p.second.second << "\n";
      }                                   


      for (auto &F: M) {
        runOnFunction (F);
      }
      printReport (errs ());

      CanReadUndef undef;
      undef.runOnModule (M);
      undef.printReport (errs ());

      errs () << " ====================================== \n";
      errs () << "   Non-analyzed (external) functions    \n";
      errs () << " ====================================== \n";
      for (auto &p: ExtFuncs) 
        errs () << p.getKey () << "\n";
      return false;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<llvm::DataLayoutPass>();
      AU.addRequired<llvm::CallGraphWrapperPass>();
      AU.addRequired<llvm::TargetLibraryInfo>();
      AU.addPreserved<CallGraphWrapperPass> ();
    }

                                                            
    void printReport (raw_ostream &O) {
      unsigned MaxNameLen = 0, MaxValLen = 0;

      { 
        O << " ===================================== \n";
        O << "  CFG information\n";
        O << " ===================================== \n";

        // Global counters
        Counter c1  = mkCounter("Number of instructions");
        c1 += TotalInsts;
        Counter c2  = mkCounter("Number of basic blocks");
        c2 += TotalBlocks;
        Counter c3  = mkCounter("Number of joins");
        c3 += TotalJoins;
        Counter c4 = mkCounter("Number of non-external functions");
        c4 += TotalFuncs;
        Counter c5 = mkCounter("Number of (non-external) direct calls");
        c5 += TotalDirectCalls;
        Counter c6 = mkCounter("Number of (non-external) indirect calls");
        c6 += TotalIndirectCalls;
        Counter c7 = mkCounter("Number of external calls");
        c7 += TotalExternalCalls;

       std::vector<Counter> global_counters {c1, c2, c3, c4, c5, c6, c7};
        formatCounters (global_counters, MaxNameLen, MaxValLen, false);
        for (auto c: global_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getName());
        }
      }

      { // instruction counters
        MaxNameLen = MaxValLen = 0;
        std::vector<Counter> inst_counters;
        inst_counters.reserve (counters.size ());
        for(auto &p: counters) { inst_counters.push_back (p.second); }
        formatCounters (inst_counters, MaxNameLen, MaxValLen);
        O << " ===================================== \n";
        O << "  Number of each kind of instructions  \n";
        O << " ===================================== \n";
        for (auto c: inst_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getName());
        }
      }

      { // Division counters
        MaxNameLen = MaxValLen = 0;
        Counter c1 = mkCounter("Number of safe integer div/rem");
        c1 += SafeIntDiv;
        Counter c2 = mkCounter("Number of definite unsafe integer div/rem");
        c2 += UnsafeIntDiv;
        Counter c3 = mkCounter("Number of safe FP div/rem");
        c3 += SafeFPDiv;
        Counter c4 = mkCounter("Number of definite unsafe FP div/rem");
        c4 += UnsafeFPDiv;
        Counter c5 = mkCounter("Number of unknown integer div/rem");
        c5 += DivIntUnknown;
        Counter c6 = mkCounter("Number of unknown FP div/rem");
        c6 += DivFPUnknown;

        std::vector<Counter> div_counters {c1, c2, c3, c4, c5, c6};
        formatCounters (div_counters, MaxNameLen, MaxValLen,false);
        O << " ======================== \n";
        O << "   Division by zero       \n";
        O << " ======================== \n";
        for (auto c: div_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getName());
        }
      }

      { // left shift
        MaxNameLen = MaxValLen = 0;
        Counter c1 = mkCounter("Number of safe left shifts");
        c1 += SafeLeftShift;
        Counter c2 = mkCounter("Number of definite unsafe left shifts");
        c2 += UnsafeLeftShift;
        Counter c3 = mkCounter("Number of unknown left shifts");
        c3 += UnknownLeftShift;
        std::vector<Counter> lsh_counters {c1, c2, c3};
        formatCounters (lsh_counters, MaxNameLen, MaxValLen,false);
        O << " ======================== \n";
        O << "   Oversized Left Shifts  \n";
        O << " ======================== \n";
        for (auto c: lsh_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getName());
        }
      }


      { // Memory counters
        MaxNameLen = MaxValLen = 0;
        Counter c1 = mkCounter("Total Number of memory accesses");
        c1 += TotalMemAccess;
        Counter c2 = mkCounter("Number of safe memory accesses");
        c2 += SafeMemAccess;
        Counter c3 = mkCounter("Number of unknown memory accesses");
        c3 += MemUnknown;
        std::vector<Counter> mem_counters {c1, c2, c3};
        formatCounters (mem_counters, MaxNameLen, MaxValLen,false);
        O << " ================================= \n";
        O << "   Out-of-bounds memory accesses    \n";
        O << " ================================= \n";
        for (auto c: mem_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getName());
        }
      }
    }

    virtual const char* getPassName () const {return "Profiler";}
  };

  char Profiler::ID = 0;

  ModulePass *createProfilerPass() { 
    return new Profiler(); 
  }

  } // end namespace crabllvm




