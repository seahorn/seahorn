#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/CommandLine.h"

#include "clam/CfgBuilder.hh"
#include "clam/Clam.hh"
#include "clam/ClamQueryAPI.hh"
#include "clam/CrabDomainParser.hh"
#include "clam/SeaDsaHeapAbstraction.hh"
#include "crab/domains/abstract_domain_params.hpp"
#include "crab/support/stats.hpp"

#include "seahorn/Analysis/CrabAnalysis.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Support/Stats.hh"

namespace {
clam::CrabDomain::Type CrabDom;
}

// Crab reason natively about sea.is_dereferenceable without any
// lowering.
static llvm::cl::opt<bool> UseCrabCheckIsDeref(
    "crab-check-is-deref",
    llvm::cl::desc("Use crab to check sea.is_dereferenceable"),
    llvm::cl::init(false));

static llvm::cl::opt<clam::CrabDomain::Type, true, clam::CrabDomainParser>
    XCrabDom("sea-crab-dom", llvm::cl::desc("set Crab abstract domain"),
             llvm::cl::values(
                 clEnumValN(clam::CrabDomain::INTERVALS, "int",
                            "Classical interval domain (default)"),
                 clEnumValN(clam::CrabDomain::ZONES_SPLIT_DBM, "zones",
                            "Zones domain"),
                 clEnumValN(clam::CrabDomain::TERMS_INTERVALS, "term-int",
                            "Intervals with uninterpreted functions"),
                 clEnumValN(clam::CrabDomain::TERMS_ZONES, "rtz",
                            "Reduced product of term-dis-int and zones"),
                 clEnumValN(clam::CrabDomain::WRAPPED_INTERVALS, "w-int",
                            "Wrapped interval domain"),
                 clEnumValN(clam::CrabDomain::OCT, "oct", "Octagon domain"),
                 clEnumValN(clam::CrabDomain::PK, "pk",
                            "Convex Polyhedra and Linear Equalities domains")),
             llvm::cl::location(CrabDom),
             llvm::cl::init(clam::CrabDomain::ZONES_SPLIT_DBM));

namespace seahorn {
using namespace llvm;

void CrabAnalysis::initCrabAnalysis(
    const llvm::Module &M, seadsa::GlobalAnalysis &dsa,
    llvm::TargetLibraryInfoWrapperPass &tliPass) {

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
  m_crab = std::make_unique<clam::InterGlobalClam>(M, *m_cfg_builder_man);
}

void CrabAnalysis::runCrabAnalysis() {
  /// Set Crab parameters
  clam::AnalysisParams aparams;
  aparams.run_inter = true;
  aparams.check = clam::CheckerKind::NOCHECKS;
  aparams.widening_delay = 2; // set to delay widening
  aparams.dom = CrabDom;      // set Crab abstract domain

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
    const llvm::Module &M, seadsa::GlobalAnalysis &dsa,
    llvm::TargetLibraryInfoWrapperPass &tliPass) {
  LOG("crab-analysis", errs() << "Start Running Crab Analysis\n";);

  // Step 1. Set up crab analysis
  initCrabAnalysis(M, dsa, tliPass);
  // Step 2. Run crab analysis
  runCrabAnalysis();
  LOG("crab-analysis", errs() << "Crab Analysis Complete\n";);
}

const clam::InterGlobalClam &CrabAnalysis::getCrab() const {
  if (!m_crab) {
    ERR << "Error: failed to run crab analysis.";
  }
  return *m_crab;
}

clam::InterGlobalClam &CrabAnalysis::getCrab() {
  if (!m_crab) {
    ERR << "Error: failed to run crab analysis.";
  }
  return *m_crab;
}

} // namespace seahorn
