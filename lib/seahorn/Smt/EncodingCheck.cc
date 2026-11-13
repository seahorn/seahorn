#include "seahorn/Expr/Smt/EncodingCheck.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <unistd.h>
#include <unordered_set>
#include <vector>

using namespace expr;

// -- Only Z3's C API is called directly, and its error code is checked right
// -- after every call that can fail: every Z3 call, including the Z3_inc_ref
// -- of a z3++ wrapper, resets it. z3++ reports errors with exceptions or not
// -- at all, depending on how SeaHorn is compiled, so it is used only to hold
// -- references.

namespace seahorn {
namespace solver {

const char *verdictName(EncodingVerdict v) {
  switch (v) {
  case EncodingVerdict::SAME:
    return "SAME";
  case EncodingVerdict::DIFFERENT:
    return "DIFFERENT";
  case EncodingVerdict::UNDECIDED:
    return "UNDECIDED";
  case EncodingVerdict::UNCHECKED:
    return "UNCHECKED";
  }
  return "?";
}

namespace {
/// ZContext keeps its Z3 context and its encoder protected
class OpenEZ3 : public EZ3 {
public:
  explicit OpenEZ3(ExprFactory &efac) : EZ3(efac) {}
  using EZ3::get_ctx;
  using EZ3::toAst;
};

/// The error of the last Z3 call, or an empty string
std::string z3Error(Z3_context c) {
  Z3_error_code code = Z3_get_error_code(c);
  return code == Z3_OK ? std::string() : std::string(Z3_get_error_msg(c, code));
}

/// \p s on one line, cut to at most \p max characters
std::string oneLine(std::string s, size_t max = 400) {
  for (char &ch : s)
    if (ch == '\n' || ch == '\t')
      ch = ' ';
  if (s.size() > max)
    s = s.substr(0, max) + "...";
  return s;
}

std::string sortName(Z3_context c, Z3_sort s) {
  return Z3_sort_to_string(c, s);
}

/// An operator in \p e that SeaHorn's Z3 encoder cannot encode, or nullptr.
/// It has no repeat or rotate (ExprToZ.def), and on them it fails without
/// a clean error.
const char *notForZ3(Expr e) {
  std::vector<Expr> todo{e};
  std::unordered_set<ENode *> seen;
  while (!todo.empty()) {
    Expr x = todo.back();
    todo.pop_back();
    if (!seen.insert(&*x).second)
      continue;
    if (isOpX<BREPEAT>(x))
      return "repeat";
    if (isOpX<BROTATE_LEFT>(x) || isOpX<BROTATE_RIGHT>(x))
      return "rotate";
    for (unsigned i = 0, sz = x->arity(); i < sz; ++i)
      todo.push_back(x->arg(i));
  }
  return nullptr;
}

/// The names of the uninterpreted constants of \p a
void constNames(Z3_context c, Z3_ast a, std::set<std::string> &out) {
  std::vector<Z3_ast> todo{a};
  std::unordered_set<unsigned> seen;
  while (!todo.empty()) {
    Z3_ast x = todo.back();
    todo.pop_back();
    if (!seen.insert(Z3_get_ast_id(c, x)).second ||
        Z3_get_ast_kind(c, x) != Z3_APP_AST)
      continue;
    Z3_app app = Z3_to_app(c, x);
    Z3_func_decl d = Z3_get_app_decl(c, app);
    unsigned n = Z3_get_app_num_args(c, app);
    if (n == 0 && Z3_get_decl_kind(c, d) == Z3_OP_UNINTERPRETED)
      out.insert(Z3_get_symbol_string(c, Z3_get_decl_name(c, d)));
    for (unsigned i = 0; i < n; ++i)
      todo.push_back(Z3_get_app_arg(c, app, i));
  }
}
} // namespace

EncodingCheck checkSmtLibTermWithZ3(Expr e, const std::string &term,
                                    const std::vector<SmtLibConst> &consts,
                                    unsigned term_bv_width, unsigned timeout_ms,
                                    bool quantified) {
  using V = EncodingVerdict;
  if (const char *op = notForZ3(e))
    return {V::UNCHECKED,
            std::string("SeaHorn's Z3 encoder has no ") + op + " operator"};
  OpenEZ3 z3(e->efac());
  z3::context &ctx = z3.get_ctx();
  Z3_context c = ctx;

  // -- Z3's own encoding of e
  z3::ast ze = z3.toAst(e);
  if (!static_cast<Z3_ast>(ze))
    return {V::UNCHECKED, "Z3 cannot encode the expression"};
  std::string err;

  // -- the sorts must agree before the terms can be compared
  Z3_sort zs = Z3_get_sort(c, ze);
  std::string theirSort =
      term_bv_width == 0 ? std::string("Bool")
                         : "(_ BitVec " + std::to_string(term_bv_width) + ")";
  bool sameSort = term_bv_width == 0
                      ? Z3_get_sort_kind(c, zs) == Z3_BOOL_SORT
                      : Z3_get_sort_kind(c, zs) == Z3_BV_SORT &&
                            Z3_get_bv_sort_size(c, zs) == term_bv_width;
  if (!sameSort)
    return {V::DIFFERENT,
            "the sorts differ: " + theirSort + " and " + sortName(c, zs)};

  // -- the term is parsed as (assert (= rhs term)), with its constants and
  // -- a fresh constant rhs declared. rhs must differ from every constant of
  // -- both sides: Z3 identifies constants by name and sort.
  std::set<std::string> names;
  for (const SmtLibConst &k : consts)
    if (!names.insert(k.name).second)
      return {V::UNCHECKED, "two constants are named " + k.name};
  std::set<std::string> taken = names;
  constNames(c, ze, taken);
  std::string rhs = "encoding_check_rhs";
  while (taken.count(rhs))
    rhs += "_";

  std::vector<Z3_symbol> syms;
  std::vector<Z3_func_decl> decls;
  z3::func_decl_vector pinned(ctx);
  auto declare = [&](const std::string &name, Z3_sort s) {
    Z3_symbol sym = Z3_mk_string_symbol(c, name.c_str());
    Z3_func_decl d = Z3_mk_func_decl(c, sym, 0, nullptr, s);
    if (!z3Error(c).empty() || !d)
      return false;
    pinned.push_back(z3::func_decl(ctx, d));
    syms.push_back(sym);
    decls.push_back(d);
    return true;
  };
  for (const SmtLibConst &k : consts) {
    Z3_sort s =
        k.bv_width == 0 ? Z3_mk_bool_sort(c) : Z3_mk_bv_sort(c, k.bv_width);
    if (s && k.index_width != 0) {
      Z3_sort index = Z3_mk_bv_sort(c, k.index_width);
      s = index ? Z3_mk_array_sort(c, index, s) : nullptr;
    }
    if (!s || !declare(k.name, s))
      return {V::UNCHECKED, "Z3 cannot declare " + k.name + ": " + z3Error(c)};
  }
  if (!declare(rhs, zs))
    return {V::UNCHECKED, "Z3 cannot declare " + rhs + ": " + z3Error(c)};

  std::string script = "(assert (= " + rhs + " " + term + "))";
  Z3_ast_vector parsed =
      Z3_parse_smtlib2_string(c, script.c_str(), 0, nullptr, nullptr,
                              syms.size(), syms.data(), decls.data());
  err = z3Error(c);
  if (!err.empty() || !parsed) {
    // -- show the text where Z3 stopped ("line 1 column N")
    std::string near;
    auto at = err.find("column ");
    if (at != std::string::npos) {
      size_t col = std::strtoul(err.c_str() + at + 7, nullptr, 10);
      size_t from = col > 150 ? col - 150 : 0;
      near = " near: " +
             oneLine(script.substr(std::min(from, script.size()), 300));
    }
    return {V::UNCHECKED, "Z3 cannot parse the term: " + oneLine(err) + near};
  }
  z3::ast_vector pinnedParsed(ctx, parsed);
  if (Z3_ast_vector_size(c, parsed) != 1)
    return {V::UNCHECKED, "Z3 parsed " +
                              std::to_string(Z3_ast_vector_size(c, parsed)) +
                              " assertions instead of one"};
  z3::ast assignment(ctx, Z3_ast_vector_get(c, parsed, 0));

  // -- rhs = term, and rhs != Z3's encoding: unsatisfiable iff they are equal
  Z3_ast rhsRaw = Z3_mk_app(c, decls.back(), 0, nullptr);
  err = z3Error(c);
  if (!err.empty() || !rhsRaw)
    return {V::UNCHECKED, "Z3 cannot build the query: " + err};
  z3::ast rhsConst(ctx, rhsRaw);
  Z3_ast eqRaw = Z3_mk_eq(c, rhsConst, ze);
  err = z3Error(c);
  if (!err.empty() || !eqRaw)
    return {V::UNCHECKED, "Z3 cannot build the query: " + err};
  z3::ast eq(ctx, eqRaw);
  Z3_ast differRaw = Z3_mk_not(c, eq);
  err = z3Error(c);
  if (!err.empty() || !differRaw)
    return {V::UNCHECKED, "Z3 cannot build the query: " + err};
  z3::ast differ(ctx, differRaw);

  Z3_solver s = Z3_mk_solver(c);
  Z3_solver_inc_ref(c, s);
  Z3_params p = Z3_mk_params(c);
  Z3_params_inc_ref(c, p);
  Z3_params_set_uint(c, p, Z3_mk_string_symbol(c, "timeout"), timeout_ms);
  Z3_solver_set_params(c, s, p);
  err = z3Error(c);
  Z3_params_dec_ref(c, p);
  if (err.empty()) {
    Z3_solver_assert(c, s, assignment);
    err = z3Error(c);
  }
  if (err.empty()) {
    Z3_solver_assert(c, s, differ);
    err = z3Error(c);
  }
  Z3_lbool r = Z3_L_UNDEF;
  if (err.empty()) {
    r = Z3_solver_check(c, s);
    err = z3Error(c);
  }

  EncodingCheck res{V::UNCHECKED, "Z3 failed: " + err};
  if (!err.empty()) {
    // -- keep res
  } else if (r == Z3_L_FALSE) {
    res = {V::SAME, ""};
  } else if (r == Z3_L_TRUE) {
    Z3_model m = Z3_solver_get_model(c, s);
    std::string values = "(no model)";
    // -- Z3's sat is a difference only if, under its values, the other
    // -- solver's term and Z3's encoding evaluate to different values: with
    // -- lambdas, Z3 5.1.0 has answered sat with values on which they agree
    bool confirmed = false;
    // -- the other solver's term: the side of (= rhs term) that is not rhs
    Z3_ast theirs = nullptr;
    if (Z3_get_ast_kind(c, assignment) == Z3_APP_AST) {
      Z3_app app = Z3_to_app(c, assignment);
      if (Z3_get_app_num_args(c, app) == 2) {
        Z3_ast a0 = Z3_get_app_arg(c, app, 0), a1 = Z3_get_app_arg(c, app, 1);
        theirs = Z3_is_eq_ast(c, a0, rhsConst) ? a1 : a0;
      }
    }
    if (!z3Error(c).empty())
      theirs = nullptr;
    if (m && z3Error(c).empty()) {
      Z3_model_inc_ref(c, m);
      values = Z3_model_to_string(c, m);
      Z3_ast va = nullptr, vb = nullptr;
      if (theirs && Z3_model_eval(c, m, theirs, true, &va) && va &&
          z3Error(c).empty() && Z3_model_eval(c, m, ze, true, &vb) && vb &&
          z3Error(c).empty()) {
        z3::ast pa(ctx, va), pb(ctx, vb);
        confirmed =
            Z3_is_numeral_ast(c, va) && Z3_is_numeral_ast(c, vb)
                ? std::string(Z3_get_numeral_string(c, va)) !=
                      std::string(Z3_get_numeral_string(c, vb))
                : (Z3_get_bool_value(c, va) != Z3_L_UNDEF &&
                   Z3_get_bool_value(c, vb) != Z3_L_UNDEF &&
                   Z3_get_bool_value(c, va) != Z3_get_bool_value(c, vb));
      }
      if (!z3Error(c).empty())
        confirmed = false;
      Z3_model_dec_ref(c, m);
    }
    if (quantified)
      res = {V::UNDECIDED, "Z3 answers sat on a formula with quantifiers, "
                           "where its answers and values are not reliable: " +
                               oneLine(values)};
    else
      res =
          confirmed
              ? EncodingCheck{V::DIFFERENT,
                              "Z3 finds values on which they differ: " +
                                  oneLine(values)}
              : EncodingCheck{V::UNDECIDED,
                              "Z3 answers sat, but its values do not make the "
                              "two differ: " +
                                  oneLine(values)};
    // -- for debugging: the whole comparison, if a folder is named
    if (const char *dir = std::getenv("SEAHORN_ENCODING_CHECK_DUMP")) {
      static unsigned dumps = 0;
      std::string path = std::string(dir) + "/different-" +
                         std::to_string(::getpid()) + "-" +
                         std::to_string(++dumps) + ".smt2";
      if (FILE *f = std::fopen(path.c_str(), "w")) {
        std::fprintf(f,
                     "; the other solver's term:\n%s\n; Z3's encoding:\n%s\n"
                     "; values on which they differ:\n%s\n",
                     script.c_str(), Z3_ast_to_string(c, ze), values.c_str());
        std::fclose(f);
      }
    }
  } else {
    res = {V::UNDECIDED,
           std::string("Z3 gave up: ") + Z3_solver_get_reason_unknown(c, s)};
  }
  Z3_solver_dec_ref(c, s);
  return res;
}

} // namespace solver
} // namespace seahorn
