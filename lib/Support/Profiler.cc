/* 
   This pass aims at profiling a program for the purpose of checking
   certain kind of errors such as out-of-bound accesses, division by
   zero, use of uninitialized variables, etc.
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
#include "llvm/Support/CommandLine.h"
#include <boost/unordered_map.hpp>

using namespace llvm;

static llvm::cl::opt<bool>
ShowCallGraphInfo("profiler-callgraph",
        llvm::cl::desc ("Show call graph information"),
        llvm::cl::init (false));

static llvm::cl::opt<bool>
DisplayDeclarations("profiler-list-declarations",
        llvm::cl::desc ("List all the function declarations"),
        llvm::cl::init (false));

#include "llvm/IR/Instruction.def"

namespace seahorn {

  struct Counter {
    const char*Name;
    const char* Desc;
    unsigned int Value;
    Counter (): Name(""), Desc (""), Value(0)  { }
    Counter (const char *name): Name(name), Desc (name), Value(0) { }
    Counter (const char *name, const char *desc): Name(name), Desc (desc), Value(0) { }
    bool operator<(const Counter&o) const 
    { return (std::strcmp(getName(), o.getName()) < 0); }
    bool operator==(const Counter&o) const 
    { return (std::strcmp(getName(), o.getName()) == 0); }
    unsigned int getValue() const { return Value; }
    const char *getName() const { return Name; }
    const char *getDesc() const { return Desc; }
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

    // -- to group all instruction counters
    boost::unordered_map <const char*, Counter> instCounters;
    void incrInstCounter (const char* name, unsigned val) {
      auto it = instCounters.find (name);
      if (it != instCounters.end ())
        it->second += val;
      else
        instCounters.insert (std::make_pair (name, Counter (name)));
    }

    // -- individual counters
    Counter TotalFuncs;
    Counter TotalBlocks;
    Counter TotalJoins;
    Counter TotalInsts;
    Counter TotalDirectCalls;
    Counter TotalIndirectCalls;
    Counter TotalExternalCalls;
    ///
    Counter SafeIntDiv;
    Counter SafeFPDiv;
    Counter UnsafeIntDiv;
    Counter UnsafeFPDiv;
    Counter DivIntUnknown;
    Counter DivFPUnknown;
    /// 
    Counter TotalMemInst;
    Counter MemUnknown;
    Counter SafeMemAccess;
    Counter TotalAllocations;
    Counter InBoundGEP;
    Counter MemCpy;
    Counter MemMove;
    Counter MemSet;
    ///
    Counter SafeLeftShift;
    Counter UnsafeLeftShift;
    Counter UnknownLeftShift;

    void visitFunction  (Function &F) { ++TotalFuncs; }
    void visitBasicBlock(BasicBlock &BB) { 
      ++TotalBlocks; 
      if (!BB.getSinglePredecessor ())
        ++TotalJoins;
    }

    void visitCallSite(CallSite &CS) {
      Function* callee = CS.getCalledFunction ();
      if (callee) {
        ++TotalDirectCalls;
        if (callee->isDeclaration ()) {
          ++TotalExternalCalls;
          ExtFuncs.insert (callee->getName ());
        }
      }
      else
        ++TotalIndirectCalls;

      // new, malloc, calloc, realloc, and strdup.
      if (isAllocationFn (CS.getInstruction(), TLI, true)) 
        ++TotalAllocations;
    }


    void processPointerOperand (Value* V) {
      uint64_t Size;
      if (getObjectSize (V, Size, DL, TLI, true)) {
        ++SafeMemAccess;
      } else {
        ++MemUnknown;        
      }
    }

    void processMemIntrPointerOperand (Value* V, Value*N) {
      uint64_t Size;
      if (getObjectSize (V, Size, DL, TLI, true) && isa<ConstantInt> (N)) {
        ++SafeMemAccess;
      } else {
        ++MemUnknown;        
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
          if (CI->isZero ()) ++UnsafeIntDiv;
          else ++SafeIntDiv;
        }
        else if (const ConstantFP *CFP = dyn_cast<const ConstantFP> (divisor)) {
          if (CFP->isZero ()) ++UnsafeFPDiv;
          else ++SafeFPDiv;
        }
        else {
          // cannot figure out statically
          if (BI->getOpcode () == BinaryOperator::SDiv ||
              BI->getOpcode () == BinaryOperator::UDiv ||
              BI->getOpcode () == BinaryOperator::SRem ||
              BI->getOpcode () == BinaryOperator::URem)
            ++DivIntUnknown;
          else 
            ++DivFPUnknown;
        }
      }
      else if (BI->getOpcode () == BinaryOperator::Shl) {
        // Check for oversized shift amounts
        if (const ConstantInt *CI = dyn_cast<const ConstantInt> (BI->getOperand (1))) {
          APInt shift = CI->getValue ();
          if (CI->getType ()->isIntegerTy ()) {
            APInt bitwidth (32, CI->getType ()->getIntegerBitWidth (), true);
            if (shift.slt (bitwidth))
              ++SafeLeftShift;
            else
              ++UnsafeLeftShift;
          }
          else 
            ++UnknownLeftShift;
        }
        else 
          ++UnknownLeftShift;
      }
    }

    #define HANDLE_INST(N, OPCODE, CLASS)                    \
    void visit##OPCODE(CLASS &I) {                           \
      incrInstCounter (#OPCODE, 1);                          \
      ++TotalInsts;                                          \
      if (MemTransferInst * MTI = dyn_cast<MemTransferInst>(&I)) {  \
         ++TotalMemInst;                                            \
         if (isa<MemCpyInst> (MTI)) ++MemCpy;                       \
         else if (isa<MemMoveInst> (MTI)) ++MemMove;                \
         processMemIntrPointerOperand (MTI->getSource(), MTI->getLength ()); \
         processMemIntrPointerOperand (MTI->getDest(), MTI->getLength ()); \
      }                                                             \
      else if (MemSetInst* MSI = dyn_cast<MemSetInst>(&I)) {        \
         ++TotalMemInst;                                            \
         ++MemSet;                                                  \
         processMemIntrPointerOperand (MSI->getDest(), MSI->getLength ()); \
      }                                                             \
      if (CallInst* CI = dyn_cast<CallInst>(&I)) {                  \
         CallSite CS (CI);                                          \
         visitCallSite (CS);                                        \
      }                                                             \
      else if (InvokeInst* II = dyn_cast<InvokeInst>(&I)) {         \
         CallSite CS (II);                                          \
         visitCallSite (CS);                                        \
      }                                                             \
      else if (BinaryOperator* BI = dyn_cast<BinaryOperator>(&I)) { \
         visitBinaryOperator (BI);                                  \
      }                                                             \
      else if (LoadInst* LI = dyn_cast<LoadInst>(&I)) {             \
         ++TotalMemInst;                                            \
         processPointerOperand (LI->getPointerOperand ());          \
      }                                                             \
      else if (StoreInst* SI = dyn_cast<StoreInst>(&I)) {           \
         ++TotalMemInst;                                            \
         processPointerOperand (SI->getPointerOperand ());          \
      }                                                             \
      else if (GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(&I)) { \
        if (GEP->isInBounds ()) ++InBoundGEP;                       \
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
        DL (nullptr), TLI (nullptr),
        TotalFuncs ("TotalFuncs", "Number of non-external functions"), 
        TotalBlocks ("TotalBlocks", "Number of basic blocks"), 
        TotalJoins ("TotalJoins","Number of basic blocks with more than one predecessor"), 
        TotalInsts ("TotalInsts","Number of instructions"),
        TotalDirectCalls ("TotalDirectCalls","Number of non-external direct callsites"), 
        TotalExternalCalls ("TotalExternalCalls","Number of external direct callsites"), 
        TotalIndirectCalls ("TotalIndirectCalls","Number of indirect callsites (unknown callee)"),
        ////////
        SafeIntDiv ("SafeIntDiv","Number of safe integer div/rem"), 
        SafeFPDiv ("SafeFPDiv","Number of safe FP div/rem"), 
        UnsafeIntDiv ("UnsafeIntDiv","Number of definite unsafe integer div/rem"), 
        UnsafeFPDiv ("UnsafeFPDiv","Number of definite unsafe FP div/rem"), 
        DivIntUnknown ("DivIntUnknown","Number of unknown integer div/rem"), 
        DivFPUnknown ("DivFPUnknown","Number of unknown FP div/rem"),
        /////////
        TotalMemInst ("TotalMemInst","Number of memory instructions"),
        MemUnknown ("MemUnknown","Unknown memory accesses"), 
        SafeMemAccess ("SafeMemAccess","Statically known memory accesses"), 
        TotalAllocations ("TotalAllocations","Malloc-like allocations"), 
        InBoundGEP ("InBoundGEP","Inbound GetElementPtr"),
        MemCpy ("MemCpy"),
        MemMove ("MemMove"), 
        MemSet ("MemSet"),
        /////////
        SafeLeftShift ("SafeLeftShift","Number of safe left shifts"), 
        UnsafeLeftShift ("UnsafeLeftShift", "Number of definite unsafe left shifts"), 
        UnknownLeftShift("UnknownLeftShift", "Number of unknown left shifts")
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


      if (ShowCallGraphInfo) {
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
      }                        


      for (auto &F: M) { runOnFunction (F); }
      printReport (errs ());

      CanReadUndef undef;
      undef.runOnModule (M);
      undef.printReport (errs ());

      if (DisplayDeclarations) {
        errs () << " ====================================== \n";
        errs () << "   Non-analyzed (external) functions    \n";
        errs () << " ====================================== \n";
        for (auto &p: ExtFuncs) 
          errs () << p.getKey () << "\n";
      }
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
        O << " ================\n";
        O << "  CFG analysis   \n";
        O << " ================\n";
        std::vector<Counter> cfg_counters 
           {TotalInsts, TotalBlocks, TotalJoins, TotalFuncs,
            TotalDirectCalls,TotalExternalCalls,TotalIndirectCalls};
        formatCounters (cfg_counters, MaxNameLen, MaxValLen, false);
        for (auto c: cfg_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getDesc());
        }
      }

      { // instruction counters
        MaxNameLen = MaxValLen = 0;
        std::vector<Counter> inst_counters;
        inst_counters.reserve (instCounters.size ());
        for(auto &p: instCounters) { inst_counters.push_back (p.second); }
        formatCounters (inst_counters, MaxNameLen, MaxValLen);
        O << "Number of each kind of instructions  \n";
        for (auto c: inst_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getDesc());
        }
      }

      { // Memory counters
        MaxNameLen = MaxValLen = 0;
        std::vector<Counter> mem_counters 
        {TotalMemInst,instCounters["Store"],instCounters["Load"],MemCpy,MemMove,MemSet,
         SafeMemAccess,MemUnknown,
         instCounters["GetElementPtr"],InBoundGEP,
         instCounters["Alloca"], TotalAllocations};
        formatCounters (mem_counters, MaxNameLen, MaxValLen,false);
        O << " ================================= \n";
        O << "   Memory analysis                 \n";
        O << " ================================= \n";
        for (auto c: mem_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getDesc());
        }
      }

      { // Division counters
        MaxNameLen = MaxValLen = 0;
        std::vector<Counter> div_counters 
        {SafeIntDiv,UnsafeIntDiv,SafeFPDiv,UnsafeFPDiv,DivIntUnknown,DivFPUnknown};
        formatCounters (div_counters, MaxNameLen, MaxValLen,false);
        O << " ============================== \n";
        O << "   Division by zero analysis    \n";
        O << " ============================== \n";
        for (auto c: div_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getDesc());
        }
      }

      { // left shift
        MaxNameLen = MaxValLen = 0;
        std::vector<Counter> lsh_counters {SafeLeftShift,UnsafeLeftShift,UnknownLeftShift};
        formatCounters (lsh_counters, MaxNameLen, MaxValLen,false);
        O << " =================================== \n";
        O << "   Oversized left shifts analysis    \n";
        O << " =================================== \n";
        for (auto c: lsh_counters) {
          O << format("%*u %-*s\n",
                      MaxValLen, 
                      c.getValue(),
                      MaxNameLen,
                      c.getDesc());
        }
      }
    }

    virtual const char* getPassName () const {return "Profiler";}
  };

  char Profiler::ID = 0;

  ModulePass *createProfilerPass() 
  {return new Profiler();}

} // end namespace seahorn
    



