#include "seahorn/Transforms/Instrumentation/CrabAnalysis.hh"

#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/CommandLine.h"

#include "clam/CfgBuilder.hh"
#include "clam/Clam.hh"
#include "clam/ClamQueryAPI.hh"
#include "clam/CrabDomainParser.hh"
#include "clam/SeaDsaHeapAbstraction.hh"
#include "crab/domains/abstract_domain_params.hpp"
#include "crab/support/stats.hpp"

#include "seadsa/ShadowMem.hh"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/Stats.hh"

// Crab reason natively about sea.is_dereferenceable without any
// lowering.
static llvm::cl::opt<bool> UseCrabCheckIsDeref(
    "crab-check-is-deref",
    llvm::cl::desc("Use crab to check sea.is_dereferenceable"),
    llvm::cl::init(false));

namespace seahorn {
using namespace llvm;

void CrabAnalysis::initCrabAnalysis(
    const llvm::Module &M, seadsa::ShadowMem &dsaPass,
    llvm::TargetLibraryInfoWrapperPass &tliPass) {

  auto &dsa = dsaPass.getDsaAnalysis();
  std::unique_ptr<clam::HeapAbstraction> heap_abs =
      std::make_unique<clam::SeaDsaHeapAbstraction>(M, dsa);

  // -- Set parameters for CFG
  clam::CrabBuilderParams cfg_builder_params;
  cfg_builder_params.setPrecision(clam::CrabBuilderPrecision::MEM);
  cfg_builder_params.interprocedural = true;
  cfg_builder_params.lowerUnsignedICmpIntoSigned();
  cfg_builder_params.lower_arithmetic_with_overflow_intrinsics = true;

  m_cfg_builder_man = std::make_unique<clam::CrabBuilderManager>(
      cfg_builder_params, tliPass, std::move(heap_abs));
  // -- Initialize crab for solving ranges
  m_crab = std::make_shared<clam::InterGlobalClam>(M, *m_cfg_builder_man);
}

void CrabAnalysis::runCrabAnalysis() {
  /// Set Crab parameters
  clam::AnalysisParams aparams;
  aparams.run_inter = true;
  aparams.check = clam::CheckerKind::NOCHECKS;
  aparams.widening_delay = 2; // set to delay widening
  // Note that the abstract domain is set by using clam option

  if (UseCrabCheckIsDeref) {
    crab::domains::crab_domain_params_man::get().set_param(
        "region.is_dereferenceable", "true");
  }
  /// Run the Crab analysis
  clam::ClamGlobalAnalysis::abs_dom_map_t assumptions;
  LOG("seapp-crab", aparams.print_invars = true;);
  Stats::resume("seapp.crab");
  m_crab->analyze(aparams, assumptions);
  Stats::stop("seapp.crab");
}

void CrabAnalysis::runCrabAnalysisOnModule(
    const llvm::Module &M, seadsa::ShadowMem &dsaPass,
    llvm::TargetLibraryInfoWrapperPass &tliPass) {
  LOG("crab-analysis", errs() << "Start Running Crab Analysis\n";);

  // Step 1. Set up crab analysis
  initCrabAnalysis(M, dsaPass, tliPass);
  // Step 2. Run crab analysis
  runCrabAnalysis();
  LOG("crab-analysis", errs() << "Crab Analysis Complete\n";);
}

} // namespace seahorn
