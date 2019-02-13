#include "seahorn/Transforms/Utils/DebugVerifier.hh"

#include "llvm/IR/PassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include <string>

#define DV_LOG(...) LOG("debug-verifier", __VA_ARGS__)

using namespace llvm;

namespace seahorn {

class DebugVerifierPass : public ModulePass {
public:
  static char ID;
  int m_instanceID;
  std::string m_instanceName;

  DebugVerifierPass(int instanceID = -1)
      : ModulePass(ID), m_instanceID(instanceID),
        m_instanceName("DebugVerifierPass_" + std::to_string(m_instanceID)) {}

  bool runOnModule(Module &M);
  void getAnalysisUsage(AnalysisUsage &AU) const { AU.setPreservesAll(); }
  StringRef getPassName() const override { return m_instanceName; }
};

char DebugVerifierPass::ID = 0;

bool DebugVerifierPass::runOnModule(Module &M) {
  DV_LOG(errs() << "\n~~~~~~~~~~~~~~~~ Running seahorn::DebugVerifierPass "
                << m_instanceID << " ~~~~~~~~~~~~~~~~~~~~~~ \n");

  bool brokenDebugInfo = false;
  if (llvm::verifyModule(M, &(errs()), &brokenDebugInfo)) {
    ERR << "Module verification failed!\n";
    llvm_unreachable("Terminating after failed module verification");
  }

  return false;
}

} // namespace seahorn

llvm::ModulePass *seahorn::createDebugVerifierPass(int instanceID) {
  return new seahorn::DebugVerifierPass(instanceID);
}

static llvm::RegisterPass<seahorn::DebugVerifierPass>
    X("seahorn-debug-verifier", "Seahorn Debug Verifier Pass");
