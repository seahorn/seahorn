#include "seahorn/HornWrite.hh"
#include "seahorn/ClpWrite.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/McMtWriter.hh"

#include "seahorn/config.h"

#include "llvm/Support/CommandLine.h"

namespace seahorn {
extern bool InterProcMemFmaps;
}

static llvm::cl::opt<bool> InternalWriter(
    "horn-fp-internal-writer",
    llvm::cl::desc("Use internal writer for Horn SMT2 format. (Default)"),
    llvm::cl::init(true), llvm::cl::Hidden);

enum HCFormat { SMT2, CLP, PURESMT2, MCMT };
static llvm::cl::opt<HCFormat> HornClauseFormat(
    "horn-format", llvm::cl::desc("Specify the format for Horn Clauses"),
    llvm::cl::values(
        clEnumValN(SMT2, "smt2", "SMT2 (default)"),
        clEnumValN(CLP, "clp", "CLP (Constraint Logic Programming)"),
        clEnumValN(PURESMT2, "pure-smt2", "Pure SMT-LIB2 compliant format"),
        clEnumValN(MCMT, "mcmt", "MCMT (Sally) format")),
    llvm::cl::init(SMT2));

namespace seahorn {
char HornWrite::ID = 0;

void HornWrite::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<HornifyModule>();
  AU.setPreservesAll();
}

template <typename Out, typename Key, typename Value>
void setInfo(Out &out, Key &key, Value &val) {
  out << "(set-info :" << key << " \"" << val << "\""
      << ")\n";
}

bool HornWrite::runOnModule(Module &M) {
  ScopedStats _st_("HornWrite");
  HornifyModule &hm = getAnalysis<HornifyModule>();

  HornClauseDB &origdb = hm.getHornClauseDB();
  HornClauseDB tdb(origdb.getExprFactory());
  if (InterProcMemFmaps) { // rewrite finite maps
    removeFiniteMapsHornClausesTransf(origdb, tdb);
  }
  HornClauseDB &db = InterProcMemFmaps ? tdb : origdb;
  ExprFactory &efac = hm.getExprFactory();

  if (HornClauseFormat == CLP) {
    normalizeHornClauseHeads(db);
    ClpWrite writer(db, efac);
    m_out << writer.toString();
  } else if (HornClauseFormat == MCMT) {
    // -- normalize db
    // -- create writer
    McMtWriter<llvm::raw_fd_ostream> writer(db, hm.getZContext());
    writer.write(m_out);
  } else {
    // Use local ZFixedPoint object to translate to SMT2.
    //
    // When HornWrite is called hm.getZFixedPoint () might be still
    // empty so we need to dump first the content of HornClauseDB
    // into fp.
    ZFixedPoint<EZ3> fp(hm.getZContext());
    // -- skip constraints since they are not supported.
    // -- do not skip the query
    db.loadZFixedPoint(fp, true, false);

    if (HornClauseFormat == PURESMT2) {
      // -- disable fixedpoint extension
      ZParams<EZ3> params(hm.getZContext());
      params.set(":print_fixedpoint_extensions", false);
      fp.set(params);
    }

    // -- write header
    setInfo(m_out, "original", M.getModuleIdentifier());
    std::string version("SeaHorn v.");
    version += SEAHORN_VERSION_INFO;
    setInfo(m_out, "authors", version);

    if (HornClauseFormat == PURESMT2 || !InternalWriter)
      m_out << fp.toString() << "\n";
    else
      m_out << fp << "\n";
  }

  m_out.flush();
  return false;
}

} // namespace seahorn
