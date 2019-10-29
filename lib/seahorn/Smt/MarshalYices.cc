#ifdef WITH_YICES2

#include "seahorn/Expr/Smt/MarshalYices.hh"
#include "seahorn/Expr/ExprInterp.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/lexical_cast.hpp"

using namespace expr;

namespace seahorn {
namespace solver {

static term_t encode_term_fail(Expr e, const char *error_msg) {
  if (!error_msg) {
    error_msg = yices::error_string().c_str();
  }
  std::string str;  
  raw_string_ostream str_os(str);
  str_os << "encode_term: failed on "
	 << *e
	 << "\n"
	 << error_msg
	 << "\n";
  report_fatal_error(str_os.str());
}

static void decode_term_fail(std::string error_msg, std::string yices_error_msg = "") {
  std::string str;
  raw_string_ostream str_os(str);  
  if (yices_error_msg.empty()) {
    str_os << error_msg << "\n";
  } else {
    str_os << error_msg << ":" << yices_error_msg << "\n";
  }
  report_fatal_error(str_os.str());
}

static std::string get_name(Expr e){
  Expr fname; 
  if (bind::isFapp(e)) {
    // name of the app
    fname = bind::fname (e);
    // name of the fdecl
    fname = bind::fname (fname);
  } else if (bind::isFdecl(e)) {
    // name of the fdecl
    fname = bind::fname(e);    
  } else {
    fname = e;
  }
  
  std::string sname;
  if (isOpX<STRING>(fname))
    sname = getTerm<std::string>(fname);
  else
    sname = boost::lexical_cast<std::string>(*fname);
  return sname;
}

type_t marshal_yices::encode_type(Expr e){
  
  type_t res = NULL_TYPE;
  if (isOpX<INT_TY>(e))
    res = yices_int_type();
  else if (isOpX<REAL_TY>(e))
    res = yices_real_type();
  else if (isOpX<BOOL_TY>(e))
    res = yices_bool_type();
  else if (isOpX<ARRAY_TY>(e)) {
    type_t domain = encode_type(e->left());
    type_t range = encode_type(e->right());

    if (domain != NULL_TYPE && range != NULL_TYPE) {
      res = yices_function_type1(domain, range);
    }
  } else if (isOpX<BVSORT>(e)) {
    res = yices_bv_type(bv::width(e));
    assert(res != NULL_TERM);
  } else {
    encode_term_fail(e, "Unhandled sort");
  }

  return res;
}

Expr decode_type(type_t ytau, ExprFactory &efac) {
  Expr etype = nullptr;

  if (yices_type_is_bool(ytau)) {
    etype = sort::boolTy(efac);
  } else if (yices_type_is_int(ytau)) {
    etype = sort::intTy(efac);
  } else if (yices_type_is_real(ytau)) {
    etype = sort::realTy(efac);
  } else if (yices_type_is_bitvector(ytau)) {
    uint32_t bvsize = yices_bvtype_size(ytau);
    etype = bv::bvsort(bvsize, efac);
  } else {
    char *ytaustr = yices_type_to_string(ytau, 80, 100, 0);
    yices_free_string(ytaustr);
    decode_term_fail("Unhandled sort");
  }
  return etype;
}

term_t marshal_yices::encode_term(Expr e, ycache_t &cache) {

  assert(e);

  if (isOpX<TRUE>(e))
    return yices_true();
  if (isOpX<FALSE>(e))
    return yices_false();

  /** check the cache */
  {
    auto it = cache.find(e);
    if (it != cache.end())
      return it->second;
  }

  term_t res = NULL_TERM;
  if (bind::isBVar(e)) {
    encode_term_fail(e, nullptr);
  } else if (isOpX<UINT>(e)) {
    res = yices_int64(getTerm<unsigned>(e));
  } else if (isOpX<MPQ>(e)) {
    res = yices_mpq(getTerm<expr::mpq_class>(e).get_mpq_t());
  } else if (isOpX<MPZ>(e)) {
    res = yices_mpz(getTerm<expr::mpz_class>(e).get_mpz_t());
  } else if (bv::is_bvnum(e)) {
    res = yices_bvconst_mpz(op::bv::width(e->right()),
                            getTerm<expr::mpz_class>(e->left()).get_mpz_t());
  } else if (bind::isBoolConst(e) || bind::isIntConst(e) ||
             bind::isRealConst(e) || op::bv::isBvConst(e)) {
    type_t var_type;
    if (bind::isBoolConst(e)) {
      var_type = yices_bool_type();
    } else if (bind::isIntConst(e)) {
      var_type = yices_int_type();
    } else if (bind::isRealConst(e)) {
      var_type = yices_real_type();
    } else if (op::bv::isBvConst(e)) {
      var_type = yices_bv_type(op::bv::width(e->left()->right()));
    }
    std::string sname =  get_name(e);
    const char* varname = sname.c_str();
    res =  yices_new_uninterpreted_term(var_type);
    // give a name
    int32_t errcode = yices_set_term_name(res, varname);
    if (errcode == -1) {
      encode_term_fail(e, nullptr);
    }
  } else if (bind::isConst<ARRAY_TY>(e)) {
    if (bind::isFdecl(e->left())) {
      Expr fdecl = e->left();
      type_t var_type  = encode_type(fdecl->right());
      std::string sname =  get_name(fdecl);
      const char* varname = sname.c_str();
      res =  yices_new_uninterpreted_term(var_type);
      // give a name
      int32_t errcode = yices_set_term_name(res, varname);
      if (errcode == -1) {
        encode_term_fail(e, nullptr);
      }
    } else {
      encode_term_fail(e, nullptr);
    }
  }
  /** function declaration */
  else if (bind::isFdecl(e)) {
    errs() << "Translating fdecl  " << *e << "\n";
    uint32_t arity = e->arity();
    std::vector<type_t> domain(arity);
    for (size_t i = 0; i < bind::domainSz(e); ++i) {
      type_t yt_i = encode_type(bind::domainTy(e, i));
      if (yt_i == NULL_TYPE) {
        encode_term_fail(e, "fdecl domain encode error");
        return NULL_TERM;
      }
      domain[i] = yt_i;
    }

    type_t range = encode_type(bind::rangeTy(e));
    if (range == NULL_TYPE) {
      encode_term_fail(e, "fdecl range encode error");
      return NULL_TERM;
    }

    type_t declaration_type =
        yices_function_type(e->arity(), &domain[0], range);
    assert(declaration_type != NULL_TYPE);

    res = yices_new_uninterpreted_term(declaration_type);
  }
  /** function application */
  else if (bind::isFapp(e)) {
    errs() << "Translating fapp  " << *e << "\n";    
    if (bind::isFdecl(bind::fname(e))) {
      term_t yfdecl = encode_term(bind::fname(e), cache);
      assert(yfdecl != NULL_TERM);

      uint32_t arity = e->arity() - 1;
      std::vector<term_t> args(arity);
      unsigned pos = 0;
      for (auto it = ++(e->args_begin()), end = e->args_end(); it != end;
           ++it) {
        term_t arg_i = encode_term(*it, cache);
        assert(arg_i != NULL_TERM);
        args[pos++] = arg_i;
      }

      res = yices_application(yfdecl, arity, &args[0]);
      assert(res != NULL_TERM);
    } else {
      encode_term_fail(e, nullptr);
    }
  } else if (isOpX<FORALL>(e) || isOpX<EXISTS>(e) || isOpX<LAMBDA>(e)) {
    encode_term_fail(e, nullptr);
  }

  // -- cache the result for unmarshaling
  if (res != NULL_TERM) {
    cache[e] = res;
    return res;
  }

  int arity = e->arity();

  /** other terminal expressions */
  if (arity == 0) {
    return encode_term_fail(e, "zero arity unexpected");
  } else if (arity == 1) {
    term_t arg = encode_term(e->left(), cache);

    if (isOpX<UN_MINUS>(e)) {
      res = yices_neg(arg);
    } else if (isOpX<NEG>(e)) {
      res = yices_not(arg);
    } else if (isOpX<ARRAY_DEFAULT>(e)) {
      encode_term_fail(e, "Array default term not supported in yices");
    } else if (isOpX<BNOT>(e)) {
      res = yices_bvnot(arg);
    } else if (isOpX<BNEG>(e)) {
      res = yices_bvneg(arg);
    } else if (isOpX<BREDAND>(e)) {
      res = yices_redand(arg);
    } else if (isOpX<BREDOR>(e)) {
      res = yices_redor(arg);
    } else if (isOpX<ASM>(e)) {
      res = arg;
    } else {
      encode_term_fail(e, "unhandled arity 1 case");
    }
  } else if (arity == 2) {
    term_t t1 = encode_term(e->left(), cache);
    term_t t2;    
    if (!isOpX<BSEXT>(e) && !isOpX<BZEXT>(e)) {    
      t2 = encode_term(e->right(), cache);
    }
    
    if (isOpX<AND>(e))
      res = yices_and2(t1, t2);
    else if (isOpX<OR>(e))
      res = yices_or2(t1, t2);
    else if (isOpX<IMPL>(e))
      res = yices_implies(t1, t2);
    else if (isOpX<IFF>(e))
      res = yices_iff(t1, t2);
    else if (isOpX<XOR>(e))
      res = yices_xor2(t1, t2);

    /** NumericOp */
    else if (isOpX<PLUS>(e))
      res = yices_add(t1, t2);
    else if (isOpX<MINUS>(e))
      res = yices_sub(t1, t2);
    else if (isOpX<MULT>(e))
      res = yices_mul(t1, t2);
    else if (isOpX<DIV>(e) || isOpX<IDIV>(e))
      res = yices_division(t1, t2);
    else if (isOpX<MOD>(e))
      res = yices_imod(t1, t2);
    else if (isOpX<REM>(e)) {
      encode_term_fail(e, "Integer remainder not supported in yices");
    }
    /** Compare Op */
    else if (isOpX<EQ>(e))
      res = yices_eq(t1, t2);
    else if (isOpX<NEQ>(e))
      res = yices_neq(t1, t2);
    else if (isOpX<LEQ>(e))
      res = yices_arith_leq_atom(t1, t2);
    else if (isOpX<GEQ>(e))
      res = yices_arith_geq_atom(t1, t2);
    else if (isOpX<LT>(e))
      res = yices_arith_lt_atom(t1, t2);
    else if (isOpX<GT>(e))
      res = yices_arith_gt_atom(t1, t2);
    /** Array Select */
    else if (isOpX<SELECT>(e))
      res = yices_application1(t1, t2);
    /** Array Const */
    else if (isOpX<CONST_ARRAY>(e)) {
      encode_term_fail(e, "Const array term not supported in yices");
    }
    /** Bit-Vectors */
    else if (isOpX<BSEXT>(e) || isOpX<BZEXT>(e)) {
      assert(yices_term_is_bitvector(t1));
      type_t bvt = yices_type_of_term(t1);
      uint32_t t1_sz = yices_term_bitsize(t1);
      unsigned t2_sz = bv::width(e->arg(1));
      assert(t1_sz > 0);
      assert(t1_sz < t2_sz);
      if (isOpX<BSEXT>(e)) {
        res = yices_sign_extend(t1, t2_sz - t1_sz);
      } else {
        res = yices_zero_extend(t1, t2_sz - t1_sz);
      }
    } else if (isOpX<BAND>(e))
      res = yices_bvand2(t1, t2);
    else if (isOpX<BOR>(e))
      res = yices_bvor2(t1, t2);
    else if (isOpX<BMUL>(e))
      res = yices_bvmul(t1, t2);
    else if (isOpX<BADD>(e))
      res = yices_bvadd(t1, t2);
    else if (isOpX<BSUB>(e))
      res = yices_bvsub(t1, t2);
    else if (isOpX<BSDIV>(e))
      res = yices_bvsdiv(t1, t2);
    else if (isOpX<BUDIV>(e))
      res = yices_bvdiv(t1, t2);
    else if (isOpX<BSREM>(e))
      res = yices_bvsrem(t1, t2);
    else if (isOpX<BUREM>(e))
      res = yices_bvrem(t1, t2);
    else if (isOpX<BSMOD>(e))
      res = yices_bvsmod(t1, t2);
    else if (isOpX<BULE>(e))
      res = yices_bvle_atom(t1, t2);
    else if (isOpX<BSLE>(e))
      res = yices_bvsle_atom(t1, t2);
    else if (isOpX<BUGE>(e))
      res = yices_bvge_atom(t1, t2);
    else if (isOpX<BSGE>(e))
      res = yices_bvsge_atom(t1, t2);
    else if (isOpX<BULT>(e))
      res = yices_bvlt_atom(t1, t2);
    else if (isOpX<BSLT>(e))
      res = yices_bvslt_atom(t1, t2);
    else if (isOpX<BUGT>(e))
      res = yices_bvgt_atom(t1, t2);
    else if (isOpX<BSGT>(e))
      res = yices_bvsgt_atom(t1, t2);
    else if (isOpX<BXOR>(e))
      res = yices_bvxor2(t1, t2);
    else if (isOpX<BNAND>(e))
      res = yices_bvnand(t1, t2);
    else if (isOpX<BNOR>(e))
      res = yices_bvnor(t1, t2);
    else if (isOpX<BXNOR>(e))
      res = yices_bvxnor(t1, t2);
    else if (isOpX<BCONCAT>(e))
      res = yices_bvconcat2(t1, t2);
    else if (isOpX<BSHL>(e))
      res = yices_bvshl(t1, t2);
    else if (isOpX<BLSHR>(e))
      res = yices_bvlshr(t1, t2);
    else if (isOpX<BASHR>(e))
      res = yices_bvashr(t1, t2);
    else
      return encode_term_fail(e, "unhandle binary case");
  } else if (isOpX<BEXTRACT>(e)) {
    assert(bv::high(e) >= bv::low(e));
    term_t b = encode_term(bv::earg(e), cache);
    res = yices_bvextract(b, bv::low(e), bv::high(e));
  } else if (isOpX<AND>(e) || isOpX<OR>(e) || isOpX<ITE>(e) || isOpX<XOR>(e) ||
             isOpX<PLUS>(e) || isOpX<MINUS>(e) || isOpX<MULT>(e) ||
             isOpX<STORE>(e)) {

    std::vector<term_t> args;
    for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it) {
      term_t yt = encode_term(*it, cache);
      args.push_back(yt);
    }

    if (isOp<ITE>(e)) {
      assert(e->arity() == 3);
      res = yices_ite(args[0], args[1], args[2]);
    } else if (isOp<AND>(e)) {
      res = yices_and(args.size(), &args[0]);
    } else if (isOp<OR>(e))
      res = yices_or(args.size(), &args[0]);
    else if (isOp<PLUS>(e))
      res = yices_sum(args.size(), &args[0]);
    else if (isOp<MINUS>(e)) {
      term_t rhs = yices_sum(args.size() - 1, &args[1]);
      res = yices_sub(args[0], rhs);
    } else if (isOp<MULT>(e))
      res = yices_product(args.size(), &args[0]);
    else if (isOp<STORE>(e)) {
      assert(e->arity() == 3);
      res = yices_update1(args[0], args[1], args[2]);
    } else {
      encode_term_fail(e, "supported term in yices");
    }
  } else {
    encode_term_fail(e, "Unhandled case");
  }

  if (res == NULL_TERM) {
    encode_term_fail(e, yices::error_string().c_str());
  }

  cache[e] = res;
  return res;
}

Expr marshal_yices::decode_yval(yval_t &yval, ExprFactory &efac, model_t *model,
                                bool isArray, Expr domain, Expr range) {
  Expr res = nullptr;

  // for the yices2 API
  int32_t errcode;

  /* atomic terms */
  switch (yval.node_tag) {
  case YVAL_BOOL: {
    int32_t value;
    errcode = yices_val_get_bool(model, &yval, &value);
    if (errcode == -1) {
      decode_term_fail("yices_val_get_bool failed: ", yices::error_string());
    }
    res = value == 1 ? mk<TRUE>(efac) : mk<FALSE>(efac);
    break;
  }
  case YVAL_RATIONAL: {
    // We try to get the thing as an MPZ first, if that fails, then we get an
    // MPQ.
    mpz_t z;
    mpz_init(z);
    errcode = yices_val_get_mpz(model, &yval, z);
    if (errcode != -1) {
      expr::mpz_class zpp(z);
      res = mkTerm(zpp, efac);
      mpz_clear(z);
      break;
    }
    mpz_clear(z);
    // We didn't succeed in extracting it out as a mpz, so get it as a mpz.
    mpq_t q;
    mpq_init(q);
    errcode = yices_val_get_mpq(model, &yval, q);
    if (errcode == -1) {
      decode_term_fail("yices_val_get_rat failed: ", yices::error_string());
    } else {
      expr::mpq_class qpp(q);
      res = mkTerm(qpp, efac);
    }
    mpq_clear(q);
    break;
  }
  case YVAL_BV: {
    uint32_t n = yices_val_bitsize(model, &yval);
    if (n == 0) {
      decode_term_fail("yices_val_bitsize failed");
    }

    int32_t *vals = new int32_t[n];
    errcode = yices_val_get_bv(model, &yval, vals);
    if (errcode == -1) {
      decode_term_fail("yices_val_get_bv failed: ", yices::error_string());
    }

    char *cvals = new char[n + 1];
    for (unsigned i = 0; i < n; i++) {
      cvals[n - i - 1] = vals[i] ? '1' : '0';
    }
    cvals[n] = 0;
    // string in binary representation
    std::string snum(cvals);
    res = bv::bvnum(expr::mpz_class(snum, 2), n, efac);

    delete[] vals;
    delete[] cvals;
    break;
  }
  case YVAL_SCALAR: {
    decode_term_fail("Not expecting a scalar");
  }
  case YVAL_ALGEBRAIC: {
    decode_term_fail("Not expecting an algebraic");
  }
  case YVAL_TUPLE: {
    decode_term_fail("Not expecting an tuple");
  }
  case YVAL_FUNCTION: {
    /*
      A model for a function has this form:

      1) set of mappings of the form [k1,...,kn -> v] where n is the
         dimension of the function
      2) a default value
     */
    uint32_t arity = yices_val_function_arity(model, &yval);

    if (isArray) {
      if (arity != 1) {
        decode_term_fail("Not expecting an array arity different from 1");
      }
    }

    yval_vector_t yvec; // the set of mappings
    yices_init_yval_vector(&yvec);
    yval_t def_val; // the default value
    errcode = yices_val_expand_function(model, &yval, &def_val, &yvec);
    if (errcode == -1) {
      decode_term_fail("yices_val_expand_function failed: ",
                       yices::error_string());
    }

    Expr def_val_expr =
        decode_yval(def_val, efac, model, false, nullptr, nullptr);

    // typedef for a mapping
    typedef std::pair<ExprVector, Expr> mapping_t;
    uint32_t num_mappings = yvec.size;
    // our sequence of mappings
    std::vector<mapping_t> entries(num_mappings);
    for (unsigned i = 0; i < num_mappings; i++) {
      yval_t args[arity];
      yval_t val;
      errcode = yices_val_expand_mapping(model, &yvec.data[i], args, &val);
      if (errcode == -1) {
        decode_term_fail("yices_val_expand_mapping failed: ",
                         yices::error_string());
      }

      for (unsigned j = 0; j < arity; j++) {
        Expr args_j_expr =
            decode_yval(args[j], efac, model, false, nullptr, nullptr);
        entries[i].first.push_back(args_j_expr);
      }
      entries[i].second =
          decode_yval(val, efac, model, false, nullptr, nullptr);
    }

    yices_delete_yval_vector(&yvec);
    Expr exp_i;

    if (isArray) {
      // make the array expr
      exp_i = op::array::constArray(domain, def_val_expr);
      for (unsigned i = 0; i < num_mappings; i++) {
        exp_i = op::array::store(exp_i, entries[i].first[0], entries[i].second);
      }
      res = exp_i;
    } else {
      // make the function expr
      std::vector<Expr> fentries(num_mappings);
      for (unsigned i = 0; i < num_mappings; i++) {
        fentries[i] = op::mdl::fentry(entries[i].first, entries[i].second);
      }
      res = op::mdl::ftable(fentries, def_val_expr);
    }

    break;
  }
  default:
    break;
  }

  assert(res);
  return res;
}

// This only works for simple expressions; constants (either atomic or
// uninterpreted function)
Expr marshal_yices::eval(Expr expr, ExprFactory &efac, ycache_t &cache,
                         bool complete, model_t *model) {

  term_t yt_var = encode_term(expr, cache);
  if(yt_var == NULL_TERM){
    report_fatal_error("Could not convert an Expr into a yices term");
  }

  yval_t yval;
  int32_t errcode = yices_get_value(model, yt_var, &yval);
  if (errcode == -1) {
    decode_term_fail("yices_get_value failed: ", yices::error_string());
  }

  bool is_array = false;
  Expr domain = nullptr;
  Expr range = nullptr;

  if (bind::isBoolConst(expr) || bind::isIntConst(expr) ||
      bind::isRealConst(expr) || op::bv::isBvConst(expr)) {
    // do nothing
  } else if (bind::isConst<ARRAY_TY>(expr)){
    if (bind::isFdecl(expr->left())) {
      is_array = true;
      Expr expr_type = expr->left()->right();
      domain = op::sort::arrayIndexTy(expr_type);
      range = op::sort::arrayValTy(expr_type);
    } else {
      decode_term_fail("eval failed with array constant");
    }
  } else {
    if (isOpX<NEG>(expr)) {
      return op::boolop::lneg(eval(expr->left(), efac, cache, complete, model));
    } 
    
    if (isOpX<AND>(expr) && expr->arity() == 2) {
      return op::boolop::land(eval(expr->left(), efac, cache, complete, model),
			      eval(expr->right(), efac, cache, complete, model));
    } else if (isOpX<AND>(expr) && expr->arity() > 2) {
      ExprVector r;
      for (auto it = expr->args_begin(), end = expr->args_end(); it != end; ++it) {
	r.push_back(eval(*it, efac, cache, complete, model));
      }
      return op::boolop::land(r);
    }
    
    errs() << *expr << "\n";
    decode_term_fail("eval failed: expecting only binary conjunction of constant expressions");
  }
  
  Expr res =  marshal_yices::decode_yval(yval, efac, model, is_array, domain, range);
  if (!res) {
    decode_term_fail("eval failed:", yices::error_string());
  }
  return res;
}
} // namespace yices
} // namespace seahorn

#endif
