#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Pass.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Support/DOTGraphTraits.h"
#include "llvm/Support/GraphWriter.h"

#include "seahorn/Support/CFGPrinter.hh"

using namespace llvm;

namespace seahorn {

  struct CFGPrinter : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CFGPrinter() : FunctionPass(ID) { }

    bool runOnFunction(Function &F) override {
      const LoopInfo* LI = &getAnalysis<LoopInfo>();      
      std::string Filename = F.getName().str() + ".dot";
      writeGraph (F, *LI, Filename);
      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfo>();
    }

    static bool writeGraph (Function&F, const LoopInfo& LI, std::string Filename) {
      std::error_code EC;
      raw_fd_ostream File(Filename, EC, sys::fs::F_Text);

      FunctionWrapper FW ((const Function*)&F, &LI);

      if (!EC) {
        errs() << "Writing '" << Filename << "'...";
        raw_ostream& fd = llvm::WriteGraph(File, (const FunctionWrapper*)&FW);
        errs() << "\n";
        return true;
      }
      return false;
    }
  };

  char CFGPrinter::ID = 0;

  struct CFGOnlyPrinter : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CFGOnlyPrinter() : FunctionPass(ID) { }

    bool runOnFunction(Function &F) override {
      const LoopInfo* LI = &getAnalysis<LoopInfo>();      
      std::string Filename = F.getName().str() + ".dot";
      writeGraph (F, *LI, Filename);
      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfo>();

    }

    static bool writeGraph(Function &F, const LoopInfo& LI, std::string Filename) {
      std::error_code EC;
      raw_fd_ostream File(Filename, EC, sys::fs::F_Text);
      FunctionWrapper FW ((const Function*)&F, &LI);
      if (!EC) {
        errs() << "Writing '" << Filename << "'...";
        WriteGraph(File, (const FunctionWrapper*)&FW, true);
        errs() << "\n";
        return true;
      }
      return false;
    }
  };

  char CFGOnlyPrinter::ID = 0;


  struct CFGViewer : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CFGViewer() : FunctionPass(ID) { }

    bool runOnFunction(Function &F) override {
      const LoopInfo* LI = &getAnalysis<LoopInfo>();      
      std::string Filename = F.getName().str() + ".dot";
      if (CFGPrinter::writeGraph (F, *LI, Filename))
        DisplayGraph(Filename, false, GraphProgram::DOT);        

      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfo>();
    }
  };

  char CFGViewer::ID = 0;


  struct CFGOnlyViewer : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CFGOnlyViewer() : FunctionPass(ID) { }

    bool runOnFunction(Function &F) override {
      const LoopInfo* LI = &getAnalysis<LoopInfo>();      
      std::string Filename = F.getName().str() + ".dot";
      if (CFGOnlyPrinter::writeGraph (F, *LI, Filename))
        DisplayGraph(Filename, false, GraphProgram::DOT);        

      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfo>();
    }
  };

  char CFGOnlyViewer::ID = 0;


  
  FunctionPass *createCFGPrinterPass () {
    return new CFGPrinter();
  }

  FunctionPass *createCFGOnlyPrinterPass () {
    return new CFGOnlyPrinter();
  }

  FunctionPass *createCFGViewerPass () {
    return new CFGViewer();
  }

  FunctionPass *createCFGOnlyViewerPass () {
    return new CFGOnlyViewer();
  }

} // end namespace seahorn


