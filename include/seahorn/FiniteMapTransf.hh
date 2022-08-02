#pragma once

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

using namespace expr;
using namespace expr::op;

namespace seahorn {

struct FMapExprsInfo {

  // -- set of vars of the expression being rewritten, it will
  // be updated if new vars are needed
  ExprSet &m_vars;
  // -- to cache the type of a map expr
  ExprMap &m_type;
  // -- to cache the keys definition of a map expression
  ExprMap &m_fmapKeys;
  // -- to cache the keys definition of a map expression
  ExprMap &m_fmapVarTransf;
  ExprFactory &m_efac;
  ZSimplifier<EZ3> &m_zsimp;

  // -- depth of an implication (incremented every time it is found in TD
  // visitor and decremented in the BU rewriter)
  // --- an optimization can be performed if the depth is 0 (no implications)
  int &m_dimpl;

  FMapExprsInfo(ExprSet &vars, ExprMap &types, ExprMap &fmapKeys,
                ExprMap &fmapVarTransf, int &dimpl, ExprFactory &efac,
                ZSimplifier<EZ3> &zsimp)
      : m_vars(vars), m_type(types), m_fmapKeys(fmapKeys),
        m_fmapVarTransf(fmapVarTransf), m_efac(efac), m_zsimp(zsimp),
        m_dimpl(dimpl) {}
};

class FiniteMapArgRewriter : public std::unary_function<Expr, Expr> {
  ExprSet &m_evars;
  const ExprMap &m_pred_decl_t;
  ExprFactory &m_efac;

public:
  FiniteMapArgRewriter(ExprSet &evars, const ExprMap &pred_decl_t,
                       ExprFactory &efac)
      : m_evars(evars), m_pred_decl_t(pred_decl_t), m_efac(efac){};

  Expr operator()(Expr exp);
};

// Top-down visitor to rewrite maps in arguments of predicate fapps
class FiniteMapArgsVisitor : public std::unary_function<Expr, VisitAction> {

private:
  const ExprMap &m_pred_decl_t;
  ExprFactory &m_efac;
  ExprSet &m_evars;
  int m_optEq = 0;
  std::shared_ptr<FiniteMapArgRewriter> m_rw;

public:
  FiniteMapArgsVisitor(ExprSet &evars, const ExprMap &pred_decl_t,
                       ExprFactory &efac)
      : m_evars(evars), m_pred_decl_t(pred_decl_t), m_efac(efac) {
    m_rw = std::make_shared<FiniteMapArgRewriter>(evars, m_pred_decl_t, efac);
  }
  VisitAction operator()(Expr exp);
};

Expr rewriteFiniteMapArgs(Expr e, const ExprMap &predDeclMap);
Expr rewriteFiniteMapArgs(Expr e, ExprSet &evars, const ExprMap &predDeclMap);

// Rewrites a finite map operation to remove finite map terms. The arguments
// of the operation are assumed to be already rewritten (no finite map
// terms). The rewriter needs to be initialized for every clause
class FiniteMapBodyRewriter : public std::unary_function<Expr, Expr> {
  // put Expr as a friend class have access to expr->args()??

  FMapExprsInfo m_fmei;

public:
  FiniteMapBodyRewriter(ExprSet &evars, ExprMap &expr_type, ExprMap &fmapKeys,
                        ExprMap &fmapVarVal, int &dimpl, ExprFactory &efac,
                        ZSimplifier<EZ3> &zsimp)
      : m_fmei(evars, expr_type, fmapKeys, fmapVarVal, dimpl, efac, zsimp){};

  Expr operator()(Expr exp);
};

// Bottom-up visitor to rewrite maps in bodies
class FiniteMapBodyVisitor : public std::unary_function<Expr, VisitAction> {

private:
  ExprMap m_types;
  ExprMap m_fmapDef;
  ExprMap m_fmapVarDef;
  int m_dimpl = 0;
  std::shared_ptr<FiniteMapBodyRewriter> m_rw;

public:
  FiniteMapBodyVisitor(ExprSet &evars, ExprFactory &efac,
                       ZSimplifier<EZ3> &zsimp) {
    m_rw = std::make_shared<FiniteMapBodyRewriter>(
        evars, m_types, m_fmapDef, m_fmapVarDef, m_dimpl, efac, zsimp);
  }

  VisitAction operator()(Expr exp);

private:
  bool isRewriteFiniteMapOp(Expr e);
};

namespace fmap_transf {

Expr mkGetCore(Expr fm, Expr key);
Expr mkSetCore(Expr fm, Expr key, Expr v);
Expr mkIteCore(Expr cond, Expr fm1, Expr fm2);
Expr mkSameKeysCore(Expr e);

// \brief replaces fmap consts by their values in `valmap` in `e`
Expr inlineVals(Expr e, ExprMap &valmap);

// \brief inserts the vars of an `fmap` val into `vars`
void insertVarsVal(Expr fmap, ExprSet &vars);

// \brief expands an `fmap` term to a finite map value
Expr expandToVal(Expr fmap);

// \brief builds an ite term to encode get operations. This function is used
// instead of boolop::ite to control with a flag which term is used in the then
// and else part, negating the condition if necessary (see horn-fmap-neg-cond
// flag)
Expr mkFMIte(Expr c, Expr t, Expr e);

} // namespace fmap_transf

struct InterMemStats {
  // !brief counters for encoding with InterProcMem flag
  unsigned m_n_params = 0;
  unsigned m_n_callsites = 0;
  unsigned m_n_gv = 0;

  unsigned m_fields_copied = 0;
  unsigned m_params_copied = 0;
  unsigned m_gv_copied = 0;
  unsigned m_callsites_copied = 0;

  unsigned m_node_array = 0;
  unsigned m_node_ocollapsed = 0;
  unsigned m_node_safe = 0;

  void print();

  void copyTo(InterMemStats &ims);
};

struct InterMemFMStats {
  // !brief counters for encoding with InterProcMemFMaps flag
  unsigned m_max_size = 0;
  unsigned m_max_alias = 0;
  unsigned m_n_not_unique = 0;

  void print() {
    llvm::outs() << "BRUNCH_STAT "
                 << "FMMaxSize"
                 << " " << m_max_size << "\n";
    llvm::outs() << "BRUNCH_STAT "
                 << "FMMaxAliasGet"
                 << " " << m_max_alias << "\n";
    llvm::outs() << "BRUNCH_STAT "
                 << "FMNotUniqueGets"
                 << " " << m_n_not_unique << "\n";
  }

  void copyTo(InterMemFMStats &ims) {
    ims.m_max_size = m_max_size;
    ims.m_max_alias = m_max_alias;
    ims.m_n_not_unique = m_n_not_unique;
  }

  // \brief `n_alias` is the number of possible cells that alias, if only 1,
  // then the cell is unique, because it is only accessed through one place
  inline void newAlias(unsigned n_alias) {
    if (n_alias > m_max_alias)
      m_max_alias = n_alias;
    if (n_alias > 1)
      m_n_not_unique++;
  }

  inline void newSize(unsigned size) {
    if (size > m_max_size)
      m_max_size = size;
  }
};

} // namespace seahorn
