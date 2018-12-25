#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Pass.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Support/DOTGraphTraits.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<bool>
HideShadows("cfg-hide-shadows",
            llvm::cl::desc ("Hide shadow functions and variables"),
            llvm::cl::init (false));

namespace seahorn {

  // A wrapper for a function with loop information
  struct FunctionWrapper {
    const llvm::Function* m_F; 
    const llvm::LoopInfo* m_LI;
    bool m_HideShadows;    
    FunctionWrapper (const llvm::Function* F,
		     const llvm::LoopInfo* LI,
		     bool HideShadows = false): 
        m_F (F), m_LI(LI), m_HideShadows (HideShadows) { }
  };
  
} // end namespace 

namespace llvm {

  template <> 
  struct GraphTraits<const seahorn::FunctionWrapper*> :public GraphTraits<const BasicBlock*> {
    static NodeRef getEntryNode(const seahorn::FunctionWrapper *FW) 
    {return &FW->m_F->getEntryBlock();}
    // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
    using nodes_iterator = pointer_iterator<Function::const_iterator>;
    static nodes_iterator nodes_begin(const seahorn::FunctionWrapper *FW) 
    { return nodes_iterator(FW->m_F->begin()); }
    static nodes_iterator nodes_end  (const seahorn::FunctionWrapper *FW) 
    { return nodes_iterator(FW->m_F->end()); }
    static size_t         size       (const seahorn::FunctionWrapper *FW) 
    { return FW->m_F->size(); }
  };

  template<>
  struct DOTGraphTraits<const seahorn::FunctionWrapper*> : public DefaultDOTGraphTraits {

    DOTGraphTraits (bool isSimple=false) : DefaultDOTGraphTraits(isSimple) {}

    static std::string getNodeAttributes (const BasicBlock *Node,
                                          const seahorn::FunctionWrapper * FW){

      if (FW->m_LI->isLoopHeader (const_cast<BasicBlock*>(Node)))
        return "color=blue";
      else 
        return "";
    }     

    static std::string getGraphName(const seahorn::FunctionWrapper *F) {
      return "CFG for '" + F->m_F->getName().str() + "' function";
    }

    static std::string getSimpleNodeLabel(const BasicBlock *Node,
                                          const seahorn::FunctionWrapper *) {
      if (!Node->getName().empty())
        return Node->getName().str();
      
      std::string Str;
      raw_string_ostream OS(Str);
      
      Node->printAsOperand(OS, false);
      return OS.str();
    }
    
    static std::string getCompleteNodeLabel(const BasicBlock *Node,
                                            const seahorn::FunctionWrapper *) {
      enum { MaxColumns = 80 };
      std::string Str;
      raw_string_ostream OS(Str);
      
      if (Node->getName().empty()) {
        Node->printAsOperand(OS, false);
        OS << ":";
      }
      
      OS << *Node;
      std::string OutStr = OS.str();
      if (OutStr[0] == '\n') OutStr.erase(OutStr.begin());
      
      // Process string output to make it nicer...
      unsigned ColNum = 0;
      unsigned LastSpace = 0;
      for (unsigned i = 0; i != OutStr.length(); ++i) {
        if (OutStr[i] == '\n') {                            // Left justify
          OutStr[i] = '\\';
          OutStr.insert(OutStr.begin()+i+1, 'l');
          ColNum = 0;
          LastSpace = 0;
        } else if (OutStr[i] == ';') {                      // Delete comments!
          unsigned Idx = OutStr.find('\n', i+1);            // Find end of line
          OutStr.erase(OutStr.begin()+i, OutStr.begin()+Idx);
          --i;
        } else if (ColNum == MaxColumns) {                  // Wrap lines.
          // Wrap very long names even though we can't find a space.
          if (!LastSpace)
            LastSpace = i;
          OutStr.insert(LastSpace, "\\l...");
          ColNum = i - LastSpace;
          LastSpace = 0;
          i += 3; // The loop will advance 'i' again.
        }
        else
          ++ColNum;
        if (OutStr[i] == ' ')
          LastSpace = i;
      }
      return OutStr;
    }
    
    std::string getNodeLabel(const BasicBlock *Node,
                             const seahorn::FunctionWrapper *Graph) {
      if (isSimple())
        return getSimpleNodeLabel(Node, Graph);
      else
        return getCompleteNodeLabel(Node, Graph);
    }
    
    static std::string getEdgeSourceLabel(const BasicBlock *Node,
                                          succ_const_iterator I) {
      // Label source of conditional branches with "T" or "F"
      if (const BranchInst *BI = dyn_cast<BranchInst>(Node->getTerminator()))
        if (BI->isConditional())
          return (I == succ_begin(Node)) ? "T" : "F";
      
      // Label source of switch edges with the associated value.
      if (const SwitchInst *SI = dyn_cast<SwitchInst>(Node->getTerminator())) {
        unsigned SuccNo = I.getSuccessorIndex();
        
        if (SuccNo == 0) return "def";
        
        std::string Str;
        raw_string_ostream OS(Str);
        SwitchInst::ConstCaseIt Case =
            SwitchInst::ConstCaseIt::fromSuccessorIndex(SI, SuccNo);
        OS << Case->getCaseValue()->getValue();
        return OS.str();
      }
      return "";
    }
  };
} // end namespace

namespace seahorn {

  using namespace llvm;

  struct CFGPrinter : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CFGPrinter() : FunctionPass(ID) { }

    bool runOnFunction(Function &F) override {
      const LoopInfo* LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();      
      std::string Filename = F.getName().str() + ".dot";
      writeGraph (F, *LI, Filename);
      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfoWrapperPass>();
    }

    static bool writeGraph (Function&F, const LoopInfo& LI, std::string Filename) {
      std::error_code EC;
      raw_fd_ostream File(Filename, EC, sys::fs::F_Text);

      FunctionWrapper FW ((const Function*)&F, &LI, HideShadows);

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
      const LoopInfo* LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();      
      std::string Filename = F.getName().str() + ".dot";
      writeGraph (F, *LI, Filename);
      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfoWrapperPass>();

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
      const LoopInfo* LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();      
      std::string Filename = F.getName().str() + ".dot";
      if (CFGPrinter::writeGraph (F, *LI, Filename))
        DisplayGraph(Filename, false, GraphProgram::DOT);        

      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfoWrapperPass>();
    }
  };

  char CFGViewer::ID = 0;


  struct CFGOnlyViewer : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CFGOnlyViewer() : FunctionPass(ID) { }

    bool runOnFunction(Function &F) override {
      const LoopInfo* LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();      
      std::string Filename = F.getName().str() + ".dot";
      if (CFGOnlyPrinter::writeGraph (F, *LI, Filename))
        DisplayGraph(Filename, false, GraphProgram::DOT);        

      return false;
    }

    void print(raw_ostream &OS, const Module* = nullptr) const override {}

    void getAnalysisUsage(AnalysisUsage &AU) const override {
      AU.setPreservesAll();
      AU.addRequired<LoopInfoWrapperPass>();
    }
  };

  char CFGOnlyViewer::ID = 0;


  
  Pass * createCFGPrinterPass () {
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


