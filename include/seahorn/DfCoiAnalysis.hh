/**
Computes DataFlow Cone of Influence for a given instruction
 */
#pragma once

#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/Instruction.h"
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-value"
#include <boost/hana.hpp>
#pragma clang diagnostic pop

namespace llvm {
class LoadInst;
class CallInst;
class MemTransferInst;
class AllocaInst;
} // namespace llvm

namespace seahorn {

class DfCoiAnalysis {

  llvm::DenseSet<llvm::Value *> m_coi;

  llvm::CallInst *analyzeLoad(llvm::LoadInst &LI);
  llvm::CallInst *analyzeMemTransfer(llvm::MemTransferInst &MI);
  llvm::CallInst *analyzeAllocaInst(llvm::AllocaInst &AI);

public:
  DfCoiAnalysis() {}

  /// \brief analyze COI for a given instruction
  void analyze(llvm::Value &val) {
    if (auto *user = llvm::dyn_cast<llvm::User>(&val)) {
      analyze(*user);
    } else {
      m_coi.insert(&val);
    }
  }
  void analyze(llvm::User &user);
  const llvm::DenseSet<llvm::Value *> &getCoi() const { return m_coi; }
};
} // namespace seahorn
