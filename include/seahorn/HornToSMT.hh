///
/// class HornToSMT
///

#ifndef _HORN_TOSMT__H_
#define _HORN_TOSMT__H_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "ufo/Expr.hpp"
#include "seahorn/HornClauseDB.hh"
#include "boost/logic/tribool.hpp"

#include "ufo/Smt/EZ3.hh"
#include "ufo/Smt/Z3n.hpp"

#include <memory>
#include <vector>
#include <map>

namespace seahorn
{
    using namespace llvm;
    typedef std::shared_ptr<expr::ExprMap> ExprMapPtr;
    class HornToSMT
    {
    public:
        typedef std::map<expr::ExprPair, expr::Expr> rule_map_type;
        HornToSMT (HornClauseDB& hcdb): db(hcdb) {}
        void toSMT(ufo::ZSolver<ufo::EZ3> &solver);
        HornClauseDB &getHornClauseDB() { return db; }
        rule_map_type& get_smt_rules() {return smt_rule_map;}
    private:
        expr::Expr get_std_fapp(expr::Expr fapp);
        size_t var_cnt;
        HornClauseDB& db;
        expr::ExprMap std_fapp_map;
        std::map<expr::Expr, ExprMapPtr> var_map_map;
        rule_map_type smt_rule_map;
    };
}


#endif /* _HORN_TOSMT__H_ */
