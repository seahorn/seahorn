#pragma once
/**
   Z3 interface

 */

#include "z3++.h"
#include "z3.h"

#include <sstream>

#include <unordered_map>
#include <unordered_set>

#include <boost/bimap.hpp>
#include <boost/bimap/unordered_set_of.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/logic/tribool.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/range/algorithm/sort.hpp>

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprInterp.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include <fstream>

namespace z3 {
struct ast_ptr_hash : public std::unary_function<ast, std::size_t> {
  std::size_t operator()(const ast &ast) const {
    std::hash<Z3_ast> hasher;
    return hasher(static_cast<Z3_ast>(ast));
  }
};

struct ast_ptr_equal_to : public std::binary_function<ast, ast, bool> {
  bool operator()(const ast &a1, const ast &a2) const {
    return static_cast<Z3_ast>(a1) == static_cast<Z3_ast>(a2);
  }
};
} // namespace z3

namespace seahorn {
// -- fixedpoint class is missing from z3++.h
class fixedpoint : public z3::object {
  Z3_fixedpoint m_fixedpoint;
  void init(Z3_fixedpoint f) {
    m_fixedpoint = f;
    Z3_fixedpoint_inc_ref(ctx(), f);
  }

public:
  fixedpoint(z3::context &c) : object(c) { init(Z3_mk_fixedpoint(c)); }
  fixedpoint(z3::context &c, Z3_fixedpoint s) : object(c) { init(s); }
  fixedpoint(fixedpoint const &s) : object(s) { init(s.m_fixedpoint); }
  ~fixedpoint() { Z3_fixedpoint_dec_ref(ctx(), m_fixedpoint); }
  operator Z3_fixedpoint() const { return m_fixedpoint; }
  fixedpoint &operator=(fixedpoint const &s) {
    Z3_fixedpoint_inc_ref(s.ctx(), s.m_fixedpoint);
    Z3_fixedpoint_dec_ref(ctx(), m_fixedpoint);
    m_ctx = s.m_ctx;
    m_fixedpoint = s.m_fixedpoint;
    return *this;
  }
  void set(z3::params const &p) {
    Z3_fixedpoint_set_params(ctx(), m_fixedpoint, p);
    check_error();
  }
};
} // namespace seahorn

namespace seahorn {
using namespace expr;

// forward declarations
template <typename Z> class ZSimplifier;
template <typename Z> class ZSolver;
template <typename Z> class ZModel;
template <typename Z> class ZFixedPoint;
template <typename Z> class ZParams;

inline boost::tribool z3l_to_tribool(Z3_lbool l) {
  if (l == Z3_L_TRUE)
    return true;
  else if (l == Z3_L_FALSE)
    return false;
  return boost::indeterminate;
}

template <typename Z> Expr z3_lite_simplify(Z &z3, Expr e) {
  z3::context &ctx = z3.get_ctx();
  z3::ast ast(z3.toAst(e));

  return z3.toExpr(z3::ast(ctx, Z3_simplify(ctx, ast)));
}

template <typename Z> Expr z3_simplify(Z &z3, Expr e) {
  return z3_lite_simplify(z3, e);
}

template <typename Z> Expr z3_simplify(Z &z3, Expr e, ZParams<Z> &params);

template <typename Z> Expr z3_forall_elim(Z &z3, Expr e, const ExprSet &vars) {
  z3::context &ctx = z3.get_ctx();

  z3::ast ast(z3.toAst(e));
  std::vector<Z3_app> bound(vars.size());
  z3::ast_vector pinned(ctx);

  size_t cnt = 0;
  for (Expr var : vars) {
    z3::ast a(z3.toAst(var));
    pinned.push_back(a);
    assert(a.kind() == Z3_APP_AST);

    bound[cnt++] = Z3_to_app(ctx, a);
  }

  z3::ast qexpr = z3::ast(
      ctx, Z3_mk_forall_const(ctx, 0, bound.size(), &bound[0], 0, NULL, ast));

  z3::goal goal(ctx);
  Z3_goal_assert(ctx, goal, qexpr);

  z3::tactic qe(ctx, "qe");
  ctx.check_error();

  z3::apply_result ares = qe(goal);
  ctx.check_error();

  assert(ares.size() == 1);
  goal = ares[0];

  ExprVector res;
  for (unsigned i = 0; i < goal.size(); ++i) {
    z3::ast gast(ctx, Z3_goal_formula(ctx, goal, i));
    res.push_back(z3.toExpr(gast));
  }

  return mknary<AND>(mk<TRUE>(e->efac()), res);
}

template <typename Z> Expr z3_from_smtlib(Z &z3, std::string smt) {
  z3::context &ctx = z3.get_ctx();

  z3::ast_vector av(ctx, Z3_parse_smtlib2_string(ctx, smt.c_str(), 0, NULL,
                                                 NULL, 0, NULL, NULL));
  ctx.check_error();
  z3::array<Z3_ast> args(av);
  z3::ast ast(ctx, Z3_mk_and(ctx, args.size(), args.ptr()));
  ctx.check_error();
  return z3.toExpr(ast);
}

template <typename Z> Expr z3_from_smtlib_file(Z &z3, const char *fname) {
  z3::context &ctx = z3.get_ctx();
  z3::ast_vector av(
      ctx, Z3_parse_smtlib2_file(ctx, fname, 0, NULL, NULL, 0, NULL, NULL));
  ctx.check_error();
  z3::array<Z3_ast> args(av);
  z3::ast ast(ctx, Z3_mk_and(ctx, args.size(), args.ptr()));
  ctx.check_error();
  return z3.toExpr(ast);
}

template <typename Z> std::string z3_to_smtlib(Z &z3, Expr e) {
  return z3.toSmtLib(e);
}

} // namespace seahorn

namespace seahorn {

using ast_expr_map =
    std::unordered_map<z3::ast, Expr, z3::ast_ptr_hash, z3::ast_ptr_equal_to>;
using expr_ast_map = std::unordered_map<Expr, z3::ast>;

template <typename V> void z3n_set_param(char const *p, V v) {
  z3::set_param(p, v);
}
inline void z3n_reset_params() { z3::reset_params(); }

using namespace boost;

/**
 * AST manager. Responsible for converting between Z3 ast and Expr.
 *
 * \tparam M marshaler that converts from Expr to z3::ast
 * \tparam U unmarshaler that converts from z3::ast to Expr
 */
template <typename M, typename U> class ZContext {
public:
  using expr_cache_map = boost::bimaps::unordered_set_of<Expr>;
  using z_cache_map = boost::bimaps::unordered_set_of<z3::ast, z3::ast_ptr_hash,
                                                      z3::ast_ptr_equal_to>;
  using cache_type = boost::bimap<expr_cache_map, z_cache_map>;
  using expr_cache_type = typename cache_type::left_map;
  using z_cache_type = typename cache_type::right_map;

private:
  typedef ZContext<M, U> this_type;
  ExprFactory &efac;
  z3::config m_c; // default config
  z3::context ctx;

  cache_type cache;

  void init() { Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT); }

protected:
  z3::context &get_ctx() { return ctx; }

  template <typename ExprToAstMap> z3::ast toAst(Expr e, ExprToAstMap &seen) {
    return M::marshal(e, get_ctx(), cache.left, seen);
  }
  z3::ast toAst(Expr e) {
    expr_ast_map seen;
    return toAst(e, seen);
  }

  template <typename AstToExprMap> Expr toExpr(z3::ast a, AstToExprMap &seen) {
    if (!a)
      return Expr();
    return U::unmarshal(a, get_efac(), cache.right, seen);
  }
  Expr toExpr(z3::ast a) {
    if (!a)
      return Expr();
    ast_expr_map seen;
    return toExpr(a, seen);
  }

  ExprFactory &get_efac() { return efac; }

  typedef std::unordered_set<Z3_func_decl> Z3_func_decl_set;
  typedef std::unordered_set<Z3_ast> Z3_ast_set;

  void allDecls(Z3_ast a, Z3_func_decl_set &seen, Z3_ast_set &visited) {
    if (Z3_get_ast_kind(ctx, a) != Z3_APP_AST &&
        Z3_get_ast_kind(ctx, a) != Z3_QUANTIFIER_AST)
      return;

    if (visited.count(a) > 0)
      return;
    visited.insert(a);

    if (Z3_get_ast_kind(ctx, a) == Z3_APP_AST) {
      Z3_app app = Z3_to_app(ctx, a);
      Z3_func_decl fdecl = Z3_get_app_decl(ctx, app);
      if (seen.count(fdecl) > 0)
        return;

      if (Z3_get_decl_kind(ctx, fdecl) == Z3_OP_UNINTERPRETED)
        seen.insert(fdecl);

      for (unsigned i = 0; i < Z3_get_app_num_args(ctx, app); i++)
        allDecls(Z3_get_app_arg(ctx, app, i), seen, visited);
    } else if (Z3_get_ast_kind(ctx, a) == Z3_QUANTIFIER_AST) {
      Z3_ast body = Z3_get_quantifier_body(ctx, a);
      allDecls(body, seen, visited);
    }
  }

public:
  ZContext(ExprFactory &ef) : efac(ef), ctx(m_c) { init(); }
  ZContext(ExprFactory &ef, z3::config &c) : efac(ef), ctx(c) { init(); }
  ZContext(const ZContext &) = delete;

  ~ZContext() { cache.clear(); }

  template <typename V> void set(char const *p, V v) { ctx.set(p, v); }

  std::string toSmtLib(Expr e) {
    return boost::lexical_cast<std::string>(this->toAst(e));
  }

  std::string toSmtLibDecls(Expr e) {
    std::ostringstream out;
    Z3_func_decl_set seen;
    Z3_ast_set visited;
    z3::ast a(toAst(e));
    allDecls(static_cast<Z3_ast>(a), seen, visited);
    for (Z3_func_decl fdecl : seen)
      out << Z3_func_decl_to_string(ctx, fdecl) << "\n";
    return out.str();
  }

  template <typename Range> std::string toSmtLibDecls(const Range &rng) {
    return toSmtLibDecls(mknary<AND>(mk<TRUE>(efac), rng));
  }

  ExprFactory &getExprFactory() { return get_efac(); }

  friend class ZParams<this_type>;
  friend class ZSimplifier<this_type>;
  friend class ZSolver<this_type>;
  friend class ZModel<this_type>;
  friend class ZFixedPoint<this_type>;

  friend Expr z3_lite_simplify<this_type>(this_type &z3, Expr e);
  friend Expr z3_simplify<this_type>(this_type &z3, Expr e);
  friend Expr z3_simplify<this_type>(this_type &z3, Expr e,
                                     ZParams<this_type> &params);
  friend Expr z3_forall_elim<this_type>(this_type &z3, Expr e,
                                        const ExprSet &vars);
  friend Expr z3_from_smtlib<this_type>(this_type &z3, std::string smt);
  friend Expr z3_from_smtlib_file<this_type>(this_type &z3, const char *fname);

  friend std::string z3_to_smtlib<this_type>(this_type &z3, Expr e);
};

template <typename Z> class ZModel : public std::unary_function<Expr, Expr> {
private:
  typedef ZModel<Z> this_type;

  Z &z3;
  z3::context &ctx;
  Z3_model model;

  ExprFactory &efac;

  bool isAsArray(const z3::ast &v) {
    if (v.kind() != Z3_APP_AST)
      return false;

    Z3_app app = Z3_to_app(ctx, v);
    Z3_func_decl fdecl = Z3_get_app_decl(ctx, app);
    return Z3_get_decl_kind(ctx, fdecl) == Z3_OP_AS_ARRAY;
  }

  Expr finterpToExpr(const z3::func_interp &zfunc) {
    ExprVector entries;
    for (unsigned i = 0, sz = zfunc.num_entries(); i < sz; ++i)
      entries.push_back(fentryToExpr(zfunc.entry(i)));

    z3::ast elseV(ctx, Z3_func_interp_get_else(ctx, zfunc));
    Expr res = mdl::ftable(entries, z3.toExpr(elseV));
    return res;
  }

  Expr fentryToExpr(const z3::func_entry &zentry) {
    ExprVector args;
    for (unsigned i = 0, sz = zentry.num_args(); i < sz; ++i) {
      z3::ast arg(ctx, Z3_func_entry_get_arg(ctx, zentry, i));
      args.push_back(z3.toExpr(arg));
    }
    z3::ast zval(ctx, Z3_func_entry_get_value(ctx, zentry));
    Expr res = mdl::fentry(args, z3.toExpr(zval));
    return res;
  }

public:
  ZModel(Z &z) : z3(z), ctx(z.get_ctx()), model(nullptr), efac(z.get_efac()) {}

  ZModel(Z &z, const z3::model &m)
      : z3(z), ctx(z.get_ctx()), model(m), efac(z.get_efac()) {
    Z3_model_inc_ref(ctx, model);
  }

  ZModel(const this_type &o)
      : z3(o.z3), ctx(z3.get_ctx()), model(o.model), efac(z3.get_efac()) {
    if (model)
      Z3_model_inc_ref(ctx, model);
  }

  ~ZModel() {
    if (model)
      Z3_model_dec_ref(ctx, model);
    model = nullptr;
  }

  this_type &operator=(this_type other) {
    swap(*this, other);
    return *this;
  }

  const this_type *operator->() const { return this; }

  this_type *operator->() { return this; }

  friend void swap(this_type &src, this_type &dst) {
    // -- only allow swap between models from the same context
    assert(&src.z3 == &dst.z3);
    swap(src.model, dst.model);
  }

  Expr eval(Expr e, bool completion = false) {
    assert(model);
    if (isOp<MK_STRUCT>(e)) {
      ExprVector kids;
      for (auto arg = e->args_begin(); arg != e->args_end(); ++arg) {
        kids.push_back(eval(*arg));
      }
      return strct::mk(kids);
    }
    z3::ast ast(z3.toAst(e));

    Z3_ast raw_val = NULL;
    if (Z3_model_eval(ctx, model, ast, completion, &raw_val) && raw_val) {
      z3::ast val(ctx, raw_val);
      ctx.check_error();
      if (!isAsArray(val))
        return z3.toExpr(val);
      else if (isAsArray(val)) {
        Z3_func_decl fdecl = Z3_get_as_array_func_decl(ctx, val);
        z3::func_interp zfunc(ctx, Z3_model_get_func_interp(ctx, model, fdecl));
        ctx.check_error();
        return finterpToExpr(zfunc);
      }
    }
    ctx.check_error();
    return mk<NONDET>(efac);
  }

  ExprFactory &getExprFactory() { return z3.getExprFactory(); }
  Expr operator()(Expr e) { return eval(e); }

  template <typename OutputStream>
  friend OutputStream &operator<<(OutputStream &out, this_type &model) {
    out << Z3_model_to_string(model.ctx, model.model);
    return out;
  }
};

template <typename Z> class ZParams {
private:
  typedef ZParams<Z> this_type;

  Z &z3;
  z3::context &ctx;
  z3::params params;

public:
  ZParams(Z &z) : z3(z), ctx(z.get_ctx()), params(z.get_ctx()) {}
  void set(std::string k, bool b) { params.set(k.c_str(), b); }
  void set(std::string k, unsigned n) { params.set(k.c_str(), n); }
  void set(std::string k, double n) { params.set(k.c_str(), n); }
  void set(std::string k, std::string v) {
    params.set(k.c_str(), ctx.str_symbol(v.c_str()));
  }

  void set(char const *k, bool b) { params.set(k, b); }
  void set(char const *k, unsigned n) { params.set(k, n); }
  void set(char const *k, double n) { params.set(k, n); }
  void set(char const *k, char const *v) { params.set(k, ctx.str_symbol(v)); }

  operator z3::params() const { return params; }
  operator Z3_params() const { return static_cast<Z3_params>(params); }
};

/// \brief Simplify with user-supplied parameters
template <typename Z> Expr z3_simplify(Z &z3, Expr e, ZParams<Z> &params) {
  z3::context &ctx = z3.get_ctx();
  z3::ast ast(z3.toAst(e));

  return z3.toExpr(z3::ast(ctx, Z3_simplify_ex(ctx, ast, params)));
}

template <typename Z> class ZSimplifier {
private:
  Z &z3;
  z3::context &ctx;
  ExprFactory &efac;

  ZParams<Z> m_params;
  expr_ast_map m_expr_to_ast;
  ast_expr_map m_ast_to_expr;
  std::unordered_map<Expr, Expr> m_cache;

public:
  using this_type = ZSimplifier<Z>;
  ZSimplifier(Z &z)
      : z3(z), ctx(z.get_ctx()), efac(z.get_efac()), m_params(z) {}

  ZSimplifier(const ZSimplifier &) = delete;

  Z &getContext() { return z3; }

  ZParams<Z> &params() { return m_params; }

  Expr simplify(Expr e) {
    if (strct::isStructVal(e)) {
      llvm::SmallVector<Expr, 8> kids;
      for (unsigned i = 0, sz = e->arity(); i < sz; ++i) {
        kids.push_back(simplify(e->arg(i)));
      }
      return strct::mk(kids);
    }
    auto it = m_cache.find(e);
    if (it != m_cache.end())
      return it->second;

    z3::ast ast(z3.toAst(e, m_expr_to_ast));
    Expr res = z3.toExpr(z3::ast(ctx, Z3_simplify_ex(ctx, ast, m_params)),
                         m_ast_to_expr);
    m_cache.insert({e, res});

    return res;
  }

  void reset() {
    m_expr_to_ast.clear();
    m_ast_to_expr.clear();
    m_cache.clear();
  }
};
template <typename Z> class ZSolver {
private:
  Z &z3;
  z3::context &ctx;
  z3::solver solver;
  ExprFactory &efac;

public:
  typedef ZSolver<Z> this_type;
  typedef ZModel<Z> Model;

  ZSolver(Z &z)
      : z3(z), ctx(z.get_ctx()), solver(z.get_ctx()), efac(z.get_efac()) {}

  ZSolver(Z &z, const char *logic)
      : z3(z), ctx(z.get_ctx()), solver(z.get_ctx(), logic),
        efac(z.get_efac()) {}

  Z &getContext() { return z3; }
  void set(const ZParams<Z> &p) {
    solver.set(p);
    ctx.check_error();
  }

  template <typename OutputStream> OutputStream &toSmtLib(OutputStream &out) {
    ExprVector v;
    return toSmtLibAssuming(out, v);
  }

  // same as toSmtLibAssuming but using native printer
  template <typename OutputStream, typename Range>
  OutputStream &toSmtLibAssuming_native(OutputStream &out, const Range &rng) {
    Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
    out << ";; Produced with Z3_solver_to_string()\n";
    out << Z3_solver_to_string(ctx, solver) << "\n";

    out << "(check-sat";
    for (const Expr &a : rng)
      out << " " << *a;
    out << ")\n";

    return out;
  }
  template <typename OutputStream, typename Range>
  OutputStream &toSmtLibAssuming(OutputStream &out, const Range &rng) {
#ifdef ZSOLVER_NATIVE_PRINT
    return toSmtLibAssuming_native(out, rng);
#else
    ExprVector asserts;
    assertions(std::back_inserter(asserts));
    out << z3.toSmtLibDecls(asserts);
    out << "\n";
#ifdef ZSOLVER_PRETTY_PRINT
    // -- inefficient due to lack of sharing between expressions
    for (const Expr &a : asserts)
      out << "(assert " << z3.toSmtLib(a) << ")\n";
#else
    Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
    out << "(assert " << z3.toSmtLib(mknary<AND>(mk<TRUE>(efac), asserts))
        << ")\n";
#endif
#endif
    out << "(check-sat";
    for (const Expr &a : rng)
      out << " " << *a;
    out << ")\n";
    return out;
  }

  /// Asserts (forall vars body). Work-around until quantifiers are
  /// properly supported by Expr
  template <typename Range>
  void assertForallExpr(const Range &vars, Expr body) {
    z3::ast ast(z3.toAst(body));
    std::vector<Z3_app> bound;
    bound.reserve(boost::size(vars));
    for (const Expr &v : vars)
      bound.push_back(Z3_to_app(ctx, z3.toAst(v)));

    Z3_ast forall =
        Z3_mk_forall_const(ctx, 0, bound.size(), &bound[0], 0, NULL, ast);
    Z3_solver_assert(ctx, solver, forall);
    ctx.check_error();
  }

  void assertExpr(Expr e) {
    z3::ast ast(z3.toAst(e));
    Z3_solver_assert(ctx, solver, ast);
    ctx.check_error();
  }

  /// return assertions currently in the solver
  template <typename OutputIterator> void assertions(OutputIterator out) const {
    z3::ast_vector r(ctx, Z3_solver_get_assertions(ctx, solver));
    ctx.check_error();
    for (unsigned i = 0; i < r.size(); ++i)
      *(out++) = z3.toExpr(r[i]);
  }

  boost::tribool solve() {
    boost::tribool res = z3l_to_tribool(Z3_solver_check(ctx, solver));
    ctx.check_error();
    return res;
  }

  template <typename Range> boost::tribool solveAssuming(const Range &lits) {
    z3::ast_vector av(ctx);
    for (Expr a : lits)
      av.push_back(z3.toAst(a));

    std::vector<Z3_ast> raw_av(av.size());
    for (unsigned i = 0; i < av.size(); ++i)
      raw_av[i] = Z3_ast_vector_get(ctx, av, i);

    boost::tribool res = z3l_to_tribool(
        Z3_solver_check_assumptions(ctx, solver, raw_av.size(), &raw_av[0]));
    ctx.check_error();
    return res;
  }

  template <typename OutputIterator> void unsatCore(OutputIterator out) const {
    z3::ast_vector core(ctx, Z3_solver_get_unsat_core(ctx, solver));
    ctx.check_error();

    for (unsigned i = 0; i < core.size(); ++i)
      *(out++) = z3.toExpr(core[i]);
  }

  /**
   * Combines solveAssuming(lits) and unsatCore (out)
   */
  template <typename Range, typename OutputIterator>
  boost::tribool solveAssuming(const Range &lits, OutputIterator out) {
    boost::tribool res = solveAssuming(lits);
    if (!res)
      unsatCore(out);
    return res;
  }

  Model getModel() const {
    z3::model m(ctx, Z3_solver_get_model(ctx, solver));
    return ZModel<Z>(z3, m);
  }

  void push() { solver.push(); }
  void pop(unsigned n = 1) { solver.pop(n); }
  void reset() { solver.reset(); }
};

template <typename Z> class ZFixedPoint {
private:
  typedef ZFixedPoint<Z> this_type;

  Z &z3;
  z3::context &ctx;
  seahorn::fixedpoint fp;
  ExprFactory &efac;

  ExprVector m_rels;
  ExprVector m_vars;
  ExprVector m_rules;
  ExprVector m_queries;

public:
  ZFixedPoint(Z &z)
      : z3(z), ctx(z.get_ctx()), fp(z.get_ctx()), efac(z.get_efac()) {}

  Z &getContext() { return z3; }

  void set(const ZParams<Z> &p) { fp.set(p); }

  void registerRelation(Expr fdecl) {
    m_rels.push_back(fdecl);
    Z3_fixedpoint_register_relation(ctx, fp,
                                    Z3_to_func_decl(ctx, z3.toAst(fdecl)));
  }

  template <typename Range> void addRule(const Range &vars, Expr rule) {
    if (isOpX<TRUE>(rule))
      return;

    assert(std::all_of(boost::begin(vars), boost::end(vars), bind::IsConst()));
    boost::copy(vars, std::back_inserter(m_vars));
    m_rules.push_back(rule);

    z3::ast ast(z3.toAst(rule));

    z3::ast qexpr(ast);

    // -- universally quantify all free variables
    if (boost::distance(vars) > 0) {
      z3::ast_vector pinned(ctx);
      pinned.resize(boost::distance(vars));
      std::vector<Z3_app> bound(boost::distance(vars));

      size_t cnt = 0;
      for (Expr v : vars) {
        z3::ast zv(z3.toAst(v));
        pinned.push_back(zv);
        bound[cnt++] = Z3_to_app(ctx, zv);
      }

      qexpr = z3::ast(ctx, Z3_mk_forall_const(ctx, 0, bound.size(), &bound[0],
                                              0, NULL, ast));
    }

    Z3_fixedpoint_add_rule(ctx, fp, qexpr, static_cast<Z3_symbol>(0));
  }

  void addQuery(Expr q) { m_queries.push_back(q); }

  void addQueries(ExprVector qs) {
    std::copy(qs.begin(), qs.end(), std::back_inserter(m_queries));
  }

  boost::tribool query(Expr q = Expr()) {
    if (q)
      m_queries.push_back(q);

    assert(m_queries.size() == 1);
    assert(bind::isBoolConst(m_queries.at(0)) || isOp<TRUE>(m_queries.at(0)) ||
           isOp<FALSE>(m_queries.at(0)));
    z3::ast ast = z3::ast(z3.toAst(m_queries.at(0)));
    tribool res = z3l_to_tribool(Z3_fixedpoint_query(ctx, fp, ast));
    ctx.check_error();
    return res;
  }

  std::string toString(Expr query = Expr()) {
    if (query)
      m_queries.push_back(query);
    assert(m_queries.size() == 1);
    assert(bind::isBoolConst(m_queries.at(0)) || isOp<TRUE>(m_queries.at(0)) ||
           isOp<FALSE>(m_queries.at(0)));
    z3::ast ast = z3::ast(z3.toAst(m_queries.at(0)));
    Z3_ast qptr = static_cast<Z3_ast>(ast);
    Z3_string str = Z3_fixedpoint_to_string(ctx, fp, 1, &qptr);
    return std::string(str);
  }

  const ExprVector &getVars() {
    boost::sort(m_vars);
    m_vars.resize(std::distance(m_vars.begin(),
                                std::unique(m_vars.begin(), m_vars.end())));
    return m_vars;
  }

  template <typename OutputStream>
  friend OutputStream &operator<<(OutputStream &out, this_type &fp) {
    for (Expr decl : fp.m_rels) {
      out << "(declare-rel " << *bind::fname(decl) << " (";
      for (unsigned i = 0; i < bind::domainSz(decl); i++) {
        Expr ty = bind::domainTy(decl, i);
        if (isOpX<BOOL_TY>(ty))
          out << "Bool ";
        else if (isOpX<REAL_TY>(ty))
          out << "Real ";
        else if (isOpX<INT_TY>(ty))
          out << "Int ";
        else if (isOpX<ARRAY_TY>(ty)) {
          out << "(Array ";
          if (isOpX<INT_TY>(sort::arrayIndexTy(ty)))
            out << "Int ";
          else if (isOpX<BVSORT>(sort::arrayIndexTy(ty))) {
            out << "(_ BitVec " << bv::width(sort::arrayIndexTy(ty)) << ") ";
          } else {
            out << "UfoUnknownSort ";
            llvm::errs() << "u1: " << *sort::arrayIndexTy(ty) << "\n";
          }
          if (isOpX<INT_TY>(sort::arrayValTy(ty)))
            out << "Int";
          else if (isOpX<BVSORT>(sort::arrayValTy(ty))) {
            out << "(_ BitVec " << bv::width(sort::arrayValTy(ty)) << ") ";
          } else {
            out << "UfoUnknownSort";
            llvm::errs() << "u2: " << *sort::arrayValTy(ty) << "\n";
          }
          out << ") ";
        } else if (isOpX<BVSORT>(ty)) {
          out << "(_ BitVec " << bv::width(ty) << ") ";
        } else {
          out << "UfoUnknownSort ";
          llvm::errs() << "u3: " << *ty << "\n";
        }
      }
      out << "))\n";
    }

    for (const Expr &v : fp.getVars()) {
      if (!bind::IsConst()(v)) {
        std::cerr << "FP var not a constant: " << *v << "\n";
      }
      assert(bind::IsConst()(v));
      out << "(declare-var " << fp.z3.toSmtLib(v) << " ";
      Expr ty = bind::typeOf(v);
      if (isOpX<BOOL_TY>(ty))
        out << "Bool ";
      else if (isOpX<REAL_TY>(ty))
        out << "Real ";
      else if (isOpX<INT_TY>(ty))
        out << "Int ";
      else if (isOpX<ARRAY_TY>(ty)) {
        out << "(Array ";
        if (isOpX<INT_TY>(sort::arrayIndexTy(ty)))
          out << "Int ";
        else if (isOpX<BVSORT>(sort::arrayIndexTy(ty))) {
          out << "(_ BitVec " << bv::width(sort::arrayIndexTy(ty)) << ") ";
        } else
          out << "UfoUnknownSort ";
        if (isOpX<INT_TY>(sort::arrayValTy(ty)))
          out << "Int";
        else if (isOpX<BVSORT>(sort::arrayValTy(ty))) {
          out << "(_ BitVec " << bv::width(sort::arrayValTy(ty)) << ") ";
        } else
          out << "UfoUnknownSort";
        out << ") ";
      } else if (isOpX<BVSORT>(ty)) {
        out << "(_ BitVec " << bv::width(ty) << ") ";
      } else
        out << "UfoUnknownSort ";
      out << ")\n";
    }

    for (Expr &rule : fp.m_rules)
      out << "(rule " << fp.z3.toSmtLib(rule) << ")\n";

    for (auto q : fp.m_queries)
      out << "(query " << fp.z3.toSmtLib(q) << ")\n";
    return out;
  }

  /**
   * Given a function application P(x, y, z) returns the set of
   * current lemmas of P in terms of variables x, y, z
   */
  Expr getCoverDelta(Expr pred, int lvl = -1) {
    assert(bind::isFapp(pred));
    z3::ast zpred(ctx, z3.toAst(pred));
    Z3_app app = Z3_to_app(ctx, zpred);

    unsigned arity = Z3_get_app_num_args(ctx, app);
    std::vector<Z3_ast> to(arity);
    for (unsigned i = 0; i < arity; ++i)
      to[i] = Z3_get_app_arg(ctx, app, i);

    Z3_func_decl zdecl = Z3_get_app_decl(ctx, app);

    z3::ast lemma(ctx, Z3_fixedpoint_get_cover_delta(ctx, fp, lvl, zdecl));

    z3::ast res(ctx, lemma);
    if (Z3_get_bool_value(ctx, res) == Z3_L_UNDEF) {
      assert(arity > 0);
      res = z3::ast(ctx, Z3_substitute_vars(ctx, lemma, arity, &to[0]));
    }

    return z3.toExpr(res);
  }

  /**
   * Given a function application P(x, y, z), adds a given lemma to
   * the given level of P. The lemma must be in terms of x, y, z
   */
  void addLemma(Expr pred, Expr lemma, bool is_invariant, int lvl = -1) {
    if (isOpX<TRUE>(lemma))
      return;

    assert(bind::isFapp(pred));
    z3::ast zpred(ctx, z3.toAst(pred));
    Z3_app app = Z3_to_app(ctx, zpred);

    if (isOpX<FALSE>(lemma)) {
      if (is_invariant)
        Z3_fixedpoint_add_invariant(ctx, fp, Z3_get_app_decl(ctx, app),
                                    Z3_mk_false(ctx));
      else
        Z3_fixedpoint_add_cover(ctx, fp, lvl, Z3_get_app_decl(ctx, app),
                                Z3_mk_false(ctx));
      ctx.check_error();
      return;
    }

    unsigned arg_size = Z3_get_app_num_args(ctx, app);
    std::vector<Z3_ast> from(arg_size);
    std::vector<Z3_ast> to(arg_size);

    // -- saves content of 'to' from garbage collection
    z3::ast_vector pinned(ctx);

    for (unsigned i = 0; i < Z3_get_app_num_args(ctx, app); ++i) {
      Z3_ast arg = Z3_get_app_arg(ctx, app, i);
      assert(Z3_is_app(ctx, arg));

      Z3_app arg_app = Z3_to_app(ctx, arg);
      Z3_func_decl arg_decl = Z3_get_app_decl(ctx, arg_app);
      assert(Z3_get_domain_size(ctx, arg_decl) == 0);

      from[i] = arg;
      to[i] = Z3_mk_bound(ctx, i, Z3_get_range(ctx, arg_decl));
      pinned.push_back(z3::ast(ctx, to[i]));
    }

    assert(from.size() > 0);
    z3::ast zlemma(ctx, Z3_substitute(ctx, z3.toAst(lemma), from.size(),
                                      &from[0], &to[0]));

    if (is_invariant)
      Z3_fixedpoint_add_invariant(ctx, fp, Z3_get_app_decl(ctx, app), zlemma);
    else
      Z3_fixedpoint_add_cover(ctx, fp, lvl, Z3_get_app_decl(ctx, app), zlemma);

    ctx.check_error();
  }

  /**
   * Given a function application P(x, y, z), adds a given lemma to
   * the given level of P. The lemma must be in terms of x, y, z
   * The lemma is used everywhere.
   */
  void addCover(Expr pred, Expr lemma, int lvl = -1) {
    addLemma(pred, lemma, false, lvl);
  }

  /**
   * Given a function application P(x, y, z), adds a given lemma to
   * the given level of P. The lemma must be in terms of x, y, z
   * The lemma is used only during the inductive invariant check.
   */
  void addInvariant(Expr pred, Expr lemma) { addLemma(pred, lemma, true, -1); }

  unsigned getNumLevels(Expr pred) {
    z3::func_decl pdecl(ctx, Z3_to_func_decl(ctx, z3.toAst(pred)));
    return Z3_fixedpoint_get_num_levels(ctx, fp, pdecl);
  }

  std::string getAnswer() {
    z3::ast res(ctx, Z3_fixedpoint_get_answer(ctx, fp));
    // return z3.toExpr (res);
    return std::string(Z3_ast_to_string(ctx, res));
  }

  /**
   ** Return a bottom-up (from query) formula of ground predicates
   ** that together from a ground derivation to query
   **/
  Expr getGroundSatAnswer() {
    z3::ast res(ctx, Z3_fixedpoint_get_ground_sat_answer(ctx, fp));
    return z3.toExpr(res);
  }

  Expr getCex() {
    z3::ast res(ctx, Z3_fixedpoint_get_answer(ctx, fp));
    return z3.toExpr(res);
  }

  void getCexRules(ExprVector &res) {
    z3::ast_vector rules(ctx, Z3_fixedpoint_get_rules_along_trace(ctx, fp));
    for (unsigned i = 0; i < rules.size(); ++i) {
      z3::ast rule(rules[i]);
      // XXX strip quantifiers because we do not support them in Expr
      if (rule.kind() == Z3_QUANTIFIER_AST)
        rule = z3::ast(ctx, Z3_get_quantifier_body(ctx, rule));
      res.push_back(z3.toExpr(rule));
    }
  }
};

} // namespace seahorn

namespace seahorn {
template <typename Z> boost::tribool z3_is_sat(Z &z3, Expr e) {
  ZSolver<Z> s(z3);
  s.assertExpr(e);
  return s.solve();
}

template <typename Z, typename Range, typename OutputIterator>
boost::tribool z3_is_sat_assuming(Z &z3, Expr e, const Range &assumptions,
                                  OutputIterator out) {
  ZSolver<Z> s(z3);

  s.assertExpr(e);
  boost::tribool res = s.solveAssuming(assumptions);
  if (!res)
    s.unsatCore(out);
  return res;
}

template <typename Z, typename Range>
boost::tribool z3_is_sat_assuming(Z &z3, Expr e, const Range &assumptions,
                                  ExprSet &result) {
  return z3_is_sat_assuming(z3, e, assumptions,
                            std::inserter(result, result.begin()));
}

template <typename Z, typename Range>
Expr z3_all_sat(Z &z3, Expr e, const Range &terms) {
  // -- z3 must be configured to produce models for this to work

  ZSolver<Z> s(z3);
  s.assertExpr(e);

  Expr res(mk<FALSE>(e->efac()));

  while (s.solve()) {
    ZModel<Z> m = s.getModel();

    Expr cube = mk<TRUE>(e->efac());
    for (Expr t : terms) {
      Expr v = m.eval(t);
      if (isOpX<TRUE>(v))
        cube = boolop::land(cube, t);
      else if (isOpX<FALSE>(v))
        cube = boolop::land(cube, boolop::lneg(t));
    }
    res = boolop::lor(res, cube);
    s.assertExpr(boolop::lneg(cube));
  }
  return res;
}

} // namespace seahorn
