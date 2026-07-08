#include "seahorn/SeaNewPmAnalyses.hh"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"

using namespace llvm;

namespace seahorn {

AnalysisKey CanFailAnalysis::Key;
AnalysisKey TopologicalOrderAnalysis::Key;
AnalysisKey CutPointGraphAnalysis::Key;

CanFailAnalysis::Result CanFailAnalysis::run(Module &M,
                                             ModuleAnalysisManager &MAM) {
  auto &CG = MAM.getResult<CallGraphAnalysis>(M);
  auto res = std::make_unique<seahorn::CanFail>();
  res->runImpl(M, CG);
  return res;
}

TopologicalOrderAnalysis::Result
TopologicalOrderAnalysis::run(Function &F, FunctionAnalysisManager &) {
  auto res = std::make_unique<seahorn::TopologicalOrder>();
  res->runImpl(F);
  return res;
}

CutPointGraphAnalysis::Result
CutPointGraphAnalysis::run(Function &F, FunctionAnalysisManager &FAM) {
  auto &topo = FAM.getResult<TopologicalOrderAnalysis>(F);
  auto res = std::make_unique<seahorn::CutPointGraph>();
  res->runImpl(F, *topo);
  return res;
}

AnalysisKey ControlDependenceAnalysisWrapper::Key;
AnalysisKey GateAnalysisWrapper::Key;

ControlDependenceAnalysisWrapper::Result
ControlDependenceAnalysisWrapper::run(Module &M, ModuleAnalysisManager &MAM) {
  auto &FAM =
      MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  auto res = std::make_unique<seahorn::ControlDependenceAnalysisPass>();
  for (auto &F : M)
    if (!F.isDeclaration())
      res->runImpl(F, FAM.getResult<PostDominatorTreeAnalysis>(F));
  return res;
}

GateAnalysisWrapper::Result
GateAnalysisWrapper::run(Module &M, ModuleAnalysisManager &MAM) {
  auto &cda = MAM.getResult<ControlDependenceAnalysisWrapper>(M);
  auto &FAM =
      MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  auto res = std::make_unique<seahorn::GateAnalysisPass>();
  for (auto &F : M)
    if (!F.isDeclaration())
      res->runImpl(F, cda->getControlDependenceAnalysis(F),
                   FAM.getResult<DominatorTreeAnalysis>(F),
                   FAM.getResult<PostDominatorTreeAnalysis>(F));
  return res;
}

} // namespace seahorn
