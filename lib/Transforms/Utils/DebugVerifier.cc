#include "seahorn/Transforms/Utils/DebugVerifier.hh"

#include "llvm/IR/PassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include <chrono>
#include <ctime>
#include <string>

#define DV_LOG(...) LOG("debug-verifier", __VA_ARGS__)

static llvm::cl::opt<bool>
    NoVerify("sea-verifier-noop",
             llvm::cl::desc("Don't verify in DebugVerifier (for debugging)"),
             llvm::cl::init(false));

using namespace llvm;

namespace seahorn {

class DebugVerifierPass : public ModulePass {
public:
  static char ID;
  int m_instanceID;
  std::string m_instanceName;
  StringRef m_passName;

  DebugVerifierPass(int instanceID, StringRef name)
      : ModulePass(ID), m_instanceID(instanceID),
        m_instanceName("DebugVerifierPass_" + std::to_string(m_instanceID)),
        m_passName(name) {}

  bool runOnModule(Module &M);
  void getAnalysisUsage(AnalysisUsage &AU) const { AU.setPreservesAll(); }
  StringRef getPassName() const override { return m_instanceName; }
};

char DebugVerifierPass::ID = 0;

bool DebugVerifierPass::runOnModule(Module &M) {
  DV_LOG(errs() << "\n~~~ Running seahorn::DebugVerifierPass for " << m_passName
                << " (" << m_instanceID << ") ~~~~ \n");
  DV_LOG(const auto now = std::chrono::system_clock::now();
         std::time_t time = std::chrono::system_clock::to_time_t(now);
         errs() << "\tTime: " << std::ctime(&time) << "\n");

  bool brokenDebugInfo = false;
  if (!NoVerify && llvm::verifyModule(M, &(errs()), &brokenDebugInfo)) {
    ERR << "Module verification failed!\n";
    llvm_unreachable("Terminating after failed module verification");
  }

  return false;
}

llvm::ModulePass* createDebugVerifierPass(int instanceID, StringRef name) {
  return new seahorn::DebugVerifierPass(instanceID, name);
}

} // namespace seahorn
