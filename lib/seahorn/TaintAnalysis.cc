#include "seahorn/TaintAnalysis.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornToSMT.hh"
#include "seahorn/HornUnroll.hh"
#include "llvm/Support/CommandLine.h"

#include "ufo/Smt/EZ3.hh"
#include "ufo/Smt/Z3n.hpp"

#include <vector>
#include <utility>
#include <fstream>

#include <boost/lexical_cast.hpp>
#include "boost/unordered_map.hpp"
#include <boost/unordered_set.hpp>
#include "boost/range/algorithm/reverse.hpp"

using namespace llvm;


static void debug_breakpoint()
{
  llvm::errs()<<"******* entering debug break point******\n";
}

namespace seahorn
{
    using namespace expr;
    char TaintAnalysisPass::ID = 0;

    void TaintAnalysis::printCex(ZFixedPoint<EZ3> &fp)
    {
        ExprVector rules;
        fp.getCexRules (rules);
        boost::reverse (rules);
        for (Expr r : rules)
        {
          Expr src;
          Expr dst;

          if (isOpX<IMPL> (r))
          {
            dst = r->arg (1);
            r = r->arg (0);
            src = isOpX<AND> (r) ? r->arg (0) : r;
          }
          else
            dst = r;

          if (src)
          {
            if (!bind::isFapp (src)) src.reset (0);
            else src = bind::fname (bind::fname (src));
          }


          if (src) outs () << *src << " --> ";

          dst = bind::fname (bind::fname (dst));
          outs () << *dst << "\n";
        }
    }
  
    bool TaintAnalysis::checkTaint (HornifyModule &hm)
    {
        {
            outs() << "First running complete solver...\n";

            HornClauseDB& db = hm.getHornClauseDB();

            ZFixedPoint<EZ3> fp (hm.getZContext ());
            ZParams<EZ3> params (hm.getZContext ());
            params.set (":engine", "spacer");
            params.set (":xform.slice", false);
            params.set (":use_heavy_mev", true);
            params.set (":reset_obligation_queue", true);
            params.set (":xform.inline-linear", false);
            params.set (":xform.inline-eager", false);
            params.set (":pdr.flexible_trace", false);
            // -- disable utvpi. It is unstable.
            params.set (":pdr.utvpi", false);
            // -- disable propagate_variable_equivalences in tail_simplifier
            params.set (":xform.tail_simplifier_pve", false);
            params.set (":xform.subsumption_checker", false);
            params.set (":order_children", 0U);
            params.set (":print_statistics", true);
            params.set (":xform.tail_simplifier_pve", false);


            //params.set (":spacer.ground_cti", true);
            //params.set (":spacer.mbqi", true);
            //params.set (":spacer.reach_dnf", true);

            fp.set(params);
            db.loadZFixedPoint (fp, true, false);
            std::string fileName = "taint.smt2";
            std::ofstream smtFile(fileName);
            smtFile << fp << "\n";
            smtFile.close();

            boost::tribool res = fp.query ();
            if (res) {
                ExprVector rules;
                fp.getCexRules (rules);
                outs () << "INF: sat " << rules.size() << "\n";
                printCex(fp);
            }
            else if (!res) outs () << "INF: unsat\n";
            else outs () << "INF: unknown";
            outs () << "\n";
        }

        for (unsigned i=1; i <= m_nBound; i++) {
            HornUnroll unroller(false);
            unroller.unroll(i, hm, hm.getHornClauseDB());

            HornClauseDB& udb = unroller.getHornClauseDB();
            outs() << "\n";
            errs() << "\n";
            ZFixedPoint<EZ3> fp (hm.getZContext ());
            ZParams<EZ3> params (hm.getZContext ());
            params.set (":engine", "spacer");
            params.set (":xform.slice", false);
            params.set (":use_heavy_mev", true);
            params.set (":reset_obligation_queue", true);
            params.set (":pdr.flexible_trace", false);
            params.set (":xform.inline-linear", true);
            params.set (":xform.inline-eager", true);
            // -- disable utvpi. It is unstable.
            params.set (":pdr.utvpi", false);
            // -- disable propagate_variable_equivalences in tail_simplifier
            params.set (":xform.tail_simplifier_pve", false);
            params.set (":xform.subsumption_checker", false);
            params.set (":order_children", 0U);

            fp.set(params);
            udb.loadZFixedPoint (fp, true, false);

            boost::tribool res = fp.query ();
            if (res) outs () << "sat at " << i;
            else if (!res) outs () << "unsat at " << i;
            else outs () << "unknown";
            outs () << "\n";

            std::string fileName = "unrolled_" + std::to_string(i) + ".smt2";
            std::ofstream unrolledSmtFile(fileName);
            unrolledSmtFile << fp << "\n";
            unrolledSmtFile.close();
            outs() << "Printed file\n";

            //if (!res) {
            //    outs() << "Taint stops propagating at bound: " << i << "\n";
            //    break;
            //}
        }

        return false;
    }

    bool TaintAnalysisPass::runOnModule(Module &M)
    {
        LOG("horn-taint-analysis", outs()<<"===TaintAnalysis::runOnModule===\n");

        HornifyModule &hm = getAnalysis<HornifyModule> ();
        m_TaintAnalysis.checkTaint(hm);

        return false;
    }

    void TaintAnalysisPass::getAnalysisUsage (AnalysisUsage &AU) const
    {
        AU.addRequired<HornifyModule> ();
        AU.setPreservesAll ();
    }
}
