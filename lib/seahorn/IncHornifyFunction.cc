#include "seahorn/IncHornifyFunction.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/LiveSymbols.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/ExprSeahorn.hh"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/CommandLine.h"


#include <boost/lexical_cast.hpp>
#include <llvm/IR/DebugInfo.h>
#include "seahorn/Support/SeaDebug.h"



  static llvm::cl::opt<std::string>
  DebugInfo("horn-df", llvm::cl::desc("Get Debug info"),
                 llvm::cl::init(""), llvm::cl::value_desc("DebugInfo"));

namespace seahorn {


/// Extract info
std::string IncHornifyFunction::extractInfo(const BasicBlock &BB, unsigned crumb) {
  std::stringstream ss;
  // errs() << "Extracting info for: " << crumb << "\n";
  std::stringstream lines;
  for (const Instruction &inst : BB) {

    // XXX: llvm 3.6
    // --- check if md is not null
    // MDNode *md = inst.getMetadata("dbg");
    // DILocation loc(md);
    // unsigned int line = loc.getLineNumber();
    // StringRef file = loc.getFilename();
    // StringRef dir = loc.getDirectory();

    // XXX: llvm 3.8
    const DebugLoc &dloc = inst.getDebugLoc ();
    unsigned line = dloc.getLine ();
    std::string file, dir;
    if (dloc.get ()) {
      file = dloc.get ()->getFilename ();
      dir = dloc.get ()->getDirectory ();
    }
    else {
      file = "unknown file";
      dir = "unknown directory";
    }

    // errs() << file << "\n";
    // errs() << inst << " | line: " << line << "\n";
    lines << line << " | ";
  }
  ss << "DINFO: " << crumb << ": " << lines.str() << "\n";
  return ss.str();
}

/// Find a function exit basic block.  Assumes that the function has
/// a unique block with return instruction
static const BasicBlock *findExitBlock(const Function &F) {
  for (const BasicBlock &bb : F)
    if (isa<ReturnInst>(bb.getTerminator()))
      return &bb;
  return NULL;
}

// WARNING: there is a similar m_bbPreds preserved for the whole
// module in HornifyModule but it cannot be used here because it
// would ignore the reachability Boolean variables.
const Expr IncHornifyFunction::bbPredicate(const BasicBlock &BB) {
  const BasicBlock *bb = &BB;
  auto it = m_bbPreds.find(bb);
  assert(it != m_bbPreds.end());
  return it->second;
}

const Expr IncHornifyFunction::declarePredicate(const BasicBlock &BB,
                                                const ExprVector &lv) {
  const BasicBlock *bb = &BB;
  Expr res = m_bbPreds[bb];
  if (res)
    return res;

  ExprVector sorts;
  sorts.reserve(lv.size() + 1);

  for (auto &v : lv) {
    assert(bind::isFapp(v));
    assert(bind::domainSz(bind::fname(v)) == 0);
    sorts.push_back(bind::typeOf(v));
  }
  sorts.push_back(mk<BOOL_TY>(m_efac));

  Expr name = mkTerm(bb, m_efac);
  res = bind::fdecl(name, sorts);

  m_bbPreds[bb] = res;
  return res;
}

inline ExprVector append(const ExprVector &a, const ExprVector &b) {
  ExprVector res(a);
  std::copy(b.begin(), b.end(), std::back_inserter(res));
  return res;
}

void IncSmallHornifyFunction::runOnFunction(Function &F) {

  const BasicBlock *exit = findExitBlock(F);
  if (!exit) {
    errs() << "The exit block of " << F.getName() << " is unreachable.\n";
    return;
  }

  const LiveSymbols &ls = m_parent.getLiveSybols(F);
  DenseMap<const BasicBlock *, unsigned> bbOrder;
  unsigned idx = 0;
  ExprVector rflags;
  std::error_code error_code;
  std::unique_ptr<llvm::tool_output_file> debug = llvm::make_unique<llvm::tool_output_file>
    (DebugInfo.c_str(), error_code, llvm::sys::fs::F_None);

  llvm::raw_ostream *dinfo_out = &debug->os ();

  std::string all_debug_info;   // all debug informations

  for (auto &BB : F) {
    std::string crumb_var =
        std::string("__r") + boost::lexical_cast<std::string>(idx);
    all_debug_info += extractInfo(BB, idx);
    rflags.push_back(bind::boolConst(mkTerm(crumb_var, m_efac)));
    bbOrder[&BB] = idx++;
    LOG("seahorn-inc",
        errs () << "Crum variable " << crumb_var << " --- " << BB.getName() << "\n");
  }

  if (!DebugInfo.empty ()) {errs() << all_debug_info;}

  for (auto &BB : F) {
    ExprVector lv = append(rflags, ls.live(&BB));

    // create predicate for the basic block
    Expr decl = declarePredicate(BB, lv);

    // register with fixedpoint
    m_db.registerRelation(decl);


    // -- attempt to extract FunctionInfo record from the current basic block
    // -- only succeeds if the current basic block is the last one
    // -- also constructs summary predicates
    if (m_interproc)
      extractFunctionInfo(BB);
  }

  BasicBlock &entry = F.getEntryBlock();
  ExprSet allVars;
  SymStore s(m_efac);
  for (const Expr &v : ls.live(&F.getEntryBlock()))
    allVars.insert(s.read(v));

  ExprVector lv;
  Expr trueE = mk<TRUE>(m_efac);
  Expr falseE = mk<FALSE>(m_efac);

  for (unsigned i = 0; i < bbOrder.size(); i++) {
    s.write(rflags[i], ((i == bbOrder[&entry]) ? trueE : falseE));
    lv.push_back(s.read(rflags[i]));
  }
  lv.insert(lv.end(), ls.live(&entry).begin(), ls.live(&entry).end());

  Expr rule = s.eval(bind::fapp(bbPredicate(entry), lv));
  rule = boolop::limp(boolop::lneg(s.read(m_sem.errorFlag(entry))), rule);
  rule = boolop::limp(trueE, rule);

  LOG("seahorn", errs() << "Adding rule : " << *rule << "\n";);

  m_db.addRule(allVars, rule);
  allVars.clear();

  ExprVector side;
  for (auto &BB : F) {
    const BasicBlock *bb = &BB;
    for (const BasicBlock *dst : succs(*bb)) {
      allVars.clear();
      s.reset();
      side.clear();

      for (const Expr &v : rflags)
        allVars.insert(s.read(v));
      for (const Expr &v : ls.live(bb))
        allVars.insert(s.read(v));

      ExprVector pre_live = append(rflags, ls.live(bb));
      Expr pre = s.eval(bind::fapp(bbPredicate(BB), pre_live));
      side.push_back(boolop::lneg((s.read(m_sem.errorFlag(BB)))));
      m_sem.execEdg(s, BB, *dst, side);

      Expr tau = mknary<AND>(trueE, side);

      expr::filter(tau, bind::IsConst(),
                   std::inserter(allVars, allVars.begin()));

      for (const Expr &v : ls.live(dst))
        allVars.insert(s.read(v));

      ExprVector post_live;
      for (unsigned i = 0; i < bbOrder.size(); i++) {
        if (i == bbOrder[dst])
          s.write(rflags[i], trueE);
        post_live.push_back(s.read(rflags[i]));
      }
      post_live.insert(post_live.end(), ls.live(dst).begin(),
                       ls.live(dst).end());

      Expr post = s.eval(bind::fapp(bbPredicate(*dst), post_live));

      LOG("seahorn",
          errs() << "Adding rule : " << *mk<IMPL>(boolop::land(pre, tau), post)
                 << "\n";);
      m_db.addRule(allVars, boolop::limp(boolop::land(pre, tau), post));
    }
  }

  allVars.clear();
  side.clear();
  s.reset();

  if (m_interproc) {
    // Add error flag exit rules
    // bb (err, V) & err -> bb_exit (err , V)
    assert(exit);
    for (auto &BB : F) {
      if (&BB == exit)
        continue;
      // XXX Can optimize. Only need the rules for BBs that trip the
      // error flag (directly or indirectly)
      s.reset();
      allVars.clear();

      const ExprVector &live = ls.live(&BB);
      for (const Expr &v : rflags)
        allVars.insert(s.read(v));
      for (const Expr &v : live)
        allVars.insert(s.read(v));

      ExprVector pre_live = append(rflags, live);
      Expr pre = s.eval(bind::fapp(bbPredicate(BB), pre_live));
      pre = boolop::land(pre, s.read(m_sem.errorFlag(BB)));

      for (const Expr &v : ls.live(exit))
        allVars.insert(s.read(v));

      ExprVector post_live;
      for (unsigned i = 0; i < bbOrder.size(); i++) {
        if (i == bbOrder[exit])
          s.write(rflags[i], trueE);
        post_live.push_back(s.read(rflags[i]));
      }
      post_live.insert(post_live.end(), ls.live(exit).begin(),
                       ls.live(exit).end());

      Expr post = s.eval(bind::fapp(bbPredicate(*exit), post_live));
      m_db.addRule(allVars, boolop::limp(pre, post));
    }
  }

  // if (F.getName ().equals ("main"))
  {
    ExprVector lv;
    for (unsigned i = 0; i < bbOrder.size(); i++) {
      if (i == bbOrder[exit] || i == bbOrder[&entry])
        s.write(rflags[i], trueE);
      lv.push_back(s.read(rflags[i]));
    }

    // lv.insert (lv.end (),
    //            ls.live (exit).begin (), ls.live (exit).end ());
    for (auto v : ls.live(exit))
      lv.push_back(s.havoc(v));

    m_db.addQuery(bind::fapp(bbPredicate(*exit), lv));
    LOG("seahorn", errs() << "Adding query : "
                          << *(bind::fapp(bbPredicate(*exit), lv)) << "\n";);
  }

  if ((!F.getName().equals("main")) && m_interproc) {
    // the summary rule
    // exit(live_at_exit) & !error.flag ->
    //                  summary(true, false, false, regions, arguments,
    //                  globals,
    //                  return)

    allVars.clear();

    const ExprVector &live = ls.live(exit);
    for (const Expr &v : live)
      allVars.insert(s.read(v));

    ExprVector pre_live = append(rflags, live);
    Expr pre = s.eval(bind::fapp(bbPredicate(*exit), pre_live));
    pre = boolop::land(pre, boolop::lneg(s.read(m_sem.errorFlag(*exit))));

    ExprVector postArgs{trueE, falseE, falseE};
    const FunctionInfo &fi = m_sem.getFunctionInfo(F);
    evalArgs(fi, m_sem, s, std::back_inserter(postArgs));
    std::copy_if(postArgs.begin() + 3, postArgs.end(),
                 std::inserter(allVars, allVars.begin()), bind::IsConst());
    Expr post = bind::fapp(fi.sumPred, postArgs);
    m_db.addRule(allVars, boolop::limp(pre, post));

    // the error rule
    // bb_exit (true, V) -> S(true, false, true, V)
    pre = boolop::land(pre->arg(0), s.read(m_sem.errorFlag(*exit)));
    postArgs[2] = trueE;
    post = bind::fapp(fi.sumPred, postArgs);
    m_db.addRule(allVars, boolop::limp(pre, post));
  }
}

} // end namespace
