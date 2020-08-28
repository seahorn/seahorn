#pragma once
#include "seahorn/Expr/EvalModel.hh"
#include "seahorn/Expr/EvalUtils.hh"
#include "seahorn/Expr/ExprCore.hh"

namespace expr {
namespace eval {
namespace evalImpl {

template <typename T> class EVR {

  std::map<Expr, BvNum<T>> m_cache;
  std::map<Expr, Expr>
      m_array; ///< maps arrays to their base (array constant, CONST_ARRAY)

  ExprVector m_lambdaStack; ///< stores the most recently visited lambda to keep
                            ///< track of bound var scopes

  EvalModel<T> *const m_evalModel;

  BvNum<T> bvUnary(Expr exp, std::function<T(T)> value) const {
    BvNum<T> child = m_cache.at(exp->first());

    T result = value(child.num);
    result = evalUtils::zeroUpperBits<T>(result, child.getWidth());

    return BvNum<T>(result, child.getWidth());
  }

  BvNum<T> bvNary(Expr exp, std::function<T(T, T)> value) const {
    BvNum<T> child1 = m_cache.at(exp->left());

    T result = child1.num;
    unsigned width = child1.getWidth();

    for (auto b = ++(exp->args_begin()), e = exp->args_end(); b != e; b++) {
      result = value(result, m_cache.at(*b).num);
      result = evalUtils::zeroUpperBits<T>(result, width);
    }

    return BvNum<T>(result, width);
  }

  bool logicalUnary(Expr exp, std::function<bool(bool)> value) const {
    bool child = (bool)m_cache.at(exp->first()).num;

    return value(child);
  }

  bool logicalNary(Expr exp, std::function<bool(bool, bool)> value) const {
    bool result = (bool)m_cache.at(exp->left()).num;

    for (auto b = ++(exp->args_begin()), e = exp->args_end(); b != e; b++) {
      result = value(result, (bool)m_cache.at(*b).num);
    }

    return result;
  }

  BvNum<T> concat(Expr exp) const {
    T concatNum = 0;
    unsigned totalWidth = 0;

    for (auto b = exp->args_begin(), e = exp->args_end(); b != e; b++) {
      BvNum<T> BvNum = m_cache.at(*b);

      totalWidth += BvNum.getWidth();

      concatNum = (concatNum << BvNum.getWidth()) | BvNum.num;
    }

    return BvNum<T>(concatNum, totalWidth);
  }

  BvNum<T> extract(Expr exp) const {
    unsigned width = (bv::high(exp) - bv::low(exp)) + 1;
    T mask = 0;

    for (int i = bv::low(exp); i <= bv::high(exp); i++) {
      mask = mask | (1 << i);
    }
    T extractArg = m_cache.at(bv::earg(exp)).num;

    T extractNum = (extractArg & mask) >> bv::low(exp);

    return BvNum<T>(extractNum, width);
  }

  BvNum<T> zext(Expr exp) const {
    BvNum<T> bnum = m_cache.at(exp->left());
    Expr bvsort = exp->right();

    unsigned width = bnum.getWidth() + bv::width(bvsort);

    return BvNum<T>(bnum.num, width);
  }

  BvNum<T> sext(Expr exp) const {

    BvNum<T> bnum = m_cache.at(exp->left());
    Expr bvsort = exp->right();

    unsigned occWidth = evalUtils::occupiedWidth<T>(bnum.num);
    unsigned width = bnum.getWidth() + bv::width(bvsort);

    T mask = evalUtils::zeroUpperBits<T>(~0, width);
    mask = evalUtils::zeroLowerBits<T>(mask, occWidth);

    return BvNum<T>(bnum.num | mask, width);
  }

  bool compare(Expr exp, std::function<bool(T, T)> value) const {
    T child1 = m_cache.at(exp->left()).num;
    T child2 = m_cache.at(exp->right()).num;

    bool result = value(child1, child2);

    return result;
  }

  bool signedCompare(Expr exp, std::function<bool(T, T)> value) const {
    BvNum<T> child1 = m_cache.at(exp->left());
    BvNum<T> child2 = m_cache.at(exp->right());

    bool result = value(child1.num, child2.num);

    // if comparision has equals and the numbers are equal
    if (result == value(child2.num, child1.num)) {
      return result;
    }

    bool signBit1 = (bool)(child1.num >> (child1.getWidth() - 1));
    bool signBit2 = (bool)(child2.num >> (child2.getWidth() - 1));

    bool flipRes =
        signBit1 || signBit2; // flip result if any of the numbers are negative

    return flipRes ? !result : result;
  }

  BvNum<T> ite(Expr exp) const {
    T condition = m_cache.at(exp->first()).num;

    BvNum<T> result;

    if (condition != 0) {
      result = m_cache.at(exp->arg(1));

    } else {
      result = m_cache.at(exp->arg(2));
    }

    return result;
  }

  BvNum<T> lambda(Expr exp) const { return m_cache.at(bind::body(exp)); }

  void store(Expr exp) {
    Expr array = m_array.at(exp->first());
    m_array.insert({exp, array});

    m_evalModel->setArrayValue(array, m_cache.at(exp->arg(1)),
                               m_cache.at(exp->arg(2)));
  }

  BvNum<T> select(Expr exp) {
    Expr array = m_array.at(exp->first());
    m_array.insert({exp, array});

    return m_evalModel->getArrayValue(array, m_cache.at(exp->right()));
  }

  template <typename A> static A convertMpz(const mpz_class &mpz) {
    return (A)(mpz.get_ui());
  }

  template <> static mpz_class convertMpz(const mpz_class &mpz) { return mpz; }

  BvNum<T> convert(Expr exp) {
    if (isOp<TRUE>(exp)) {
      return true;
    } else if (isOp<FALSE>(exp)) {
      return false;
    }

    assert(bv::isBvNum(exp));

    mpz_class mpz = bv::toMpz(exp);
    unsigned width = bv::widthBvNum(exp);

    if (mpz < (unsigned long)0) {
      // 2s complement
      mpz = evalUtils::zeroUpperBits(mpz, width);
    }

    T num = convertMpz<T>(mpz);
    return BvNum<T>(num, width);
  }

  void find(Expr exp) {
    BvNum<T> result;

    if (isOp<BNOT>(exp)) {
      auto value = [](auto val1) { return ~val1; };

      result = bvUnary(exp, value);
    } else if (isOp<BAND>(exp)) {
      auto value = [](auto val1, auto val2) { return val1 & val2; };

      result = bvNary(exp, value);
    } else if (isOp<BOR>(exp)) {
      auto value = [](auto val1, auto val2) { return val1 | val2; };

      result = bvNary(exp, value);
    } else if (isOp<BXOR>(exp)) {
      auto value = [](auto val1, auto val2) { return val1 ^ val2; };

      result = bvNary(exp, value);
    }

    else if (isOp<NEG>(exp)) {
      auto value = [](bool val1) -> bool { return !val1; };
      result = logicalUnary(exp, value);
    } else if (isOp<AND>(exp)) {
      auto value = [](bool val1, bool val2) -> bool { return val1 && val2; };
      result = logicalNary(exp, value);
    } else if (isOp<OR>(exp)) {
      auto value = [](bool val1, bool val2) -> bool { return val1 || val2; };
      result = logicalNary(exp, value);
    } else if (isOp<XOR>(exp)) {
      auto value = [](bool val1, bool val2) -> bool { return val1 != val2; };
      result = logicalNary(exp, value);
    } else if (isOp<IMPL>(exp)) {
      auto value = [](bool val1, bool val2) -> bool { return !val1 || val2; };
      result = logicalNary(exp, value);
    } else if (isOp<IFF>(exp)) {
      auto value = [](bool val1, bool val2) -> bool { return val1 == val2; };
      result = logicalNary(exp, value);
    }

    else if (isOp<BADD>(exp)) {
      auto value = [](auto val1, auto val2) { return val1 + val2; };

      result = bvNary(exp, value);
    } else if (isOp<BSUB>(exp)) {
      auto value = [](auto val1, auto val2) { return val1 - val2; };

      result = bvNary(exp, value);
    } else if (isOp<BMUL>(exp)) {
      auto value = [](auto val1, auto val2) { return val1 * val2; };

      result = bvNary(exp, value);
    } else if (isOp<BCONCAT>(exp)) {
      result = concat(exp);
    } else if (isOp<BEXTRACT>(exp)) {
      result = extract(exp);
    } else if (isOp<BZEXT>(exp)) {
      result = zext(exp);
    } else if (isOp<BSEXT>(exp)) {
      result = sext(exp);
    }

    else if (isOp<EQ>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 == val2; };
      result = compare(exp, value);
    } else if (isOp<NEQ>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 != val2; };
      result = compare(exp, value);
    }

    else if (isOp<BULT>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 < val2; };
      result = compare(exp, value);
    } else if (isOp<BULE>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 <= val2; };
      result = compare(exp, value);
    } else if (isOp<BUGT>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 > val2; };
      result = compare(exp, value);
    } else if (isOp<BUGE>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 >= val2; };
      result = compare(exp, value);
    }

    else if (isOp<BSLT>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 <= val2; };
      result = signedCompare(exp, value);
    } else if (isOp<BSLE>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 <= val2; };
      result = signedCompare(exp, value);
    } else if (isOp<BSGT>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 > val2; };
      result = signedCompare(exp, value);
    } else if (isOp<BSGE>(exp)) {
      auto value = [](auto val1, auto val2) -> bool { return val1 >= val2; };
      result = signedCompare(exp, value);
    }

    else if (isOp<ITE>(exp)) {
      result = ite(exp);
    } else if (isOp<LAMBDA>(exp)) {
      m_lambdaStack.pop_back();
      result = lambda(exp);
    } else if (isOp<STORE>(exp)) {
      store(exp);
    } else if (isOp<SELECT>(exp)) {
      result = select(exp);
    } else if (isOp<CONST_ARRAY>(exp)) {
      BvNum<T> value = m_cache.at(exp->right());

      m_evalModel->newArray(exp, value);
      m_array.insert({exp, exp});
    } else {
      ERR << "Unsupported expression: " << *exp << "\n";

      return;
    }

    m_cache.insert({exp, result});
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("ev", llvm::errs() << "post visiting " << *exp << "\n";);
    find(exp);

    return exp;
  }

public:
  EVR(EvalModel<T> *evalModel) : m_evalModel(evalModel) {}

  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("ev", llvm::errs() << "pre visiting " << *exp << "\n";);

    if (bind::isBVar(exp)) {
      // note: bound vars are updated even if they already have a value because
      // the same var might used in different scopes (different lambdas) and
      // therefore have different values

      Expr lambda = m_lambdaStack.back();
      m_cache[exp] = m_evalModel->getBoundValue(
          lambda, exp); // override any existing value

      return false;
    }

    if (m_cache.count(exp)) {
      return false;
    }

    if (bind::IsConst()(exp)) {
      if (bind::isArrayConst(exp)) {
        m_evalModel->newArray(exp);
        m_array.insert({exp, exp});
      } else {
        m_cache[exp] =
            m_evalModel->getConstantValue(exp); // override any existing value
      }

      return false;

    } else if (isOp<LAMBDA>(exp)) {
      m_evalModel->newLambda(exp);
      m_lambdaStack.push_back(exp);
    } else if (bv::is_bvnum(exp) || isOp<TRUE>(exp) || isOp<FALSE>(exp)) {
      m_cache.insert({exp, convert(exp)});

      return false;
    } else if (isOp<UINT>(exp) || isOp<MPZ>(exp) || isOp<BVSORT>(exp)) {
      return false;
    }

    return true;
  }

  Expr operator()(Expr exp) { return postVisit(exp); }

  T getValue(Expr exp) { return m_cache.at(exp).num; }
};

template <typename T> class EV : public std::unary_function<Expr, VisitAction> {
  std::shared_ptr<EVR<T>> m_rw;

public:
  EV(EvalModel<T> *evalModel) : m_rw(std::make_shared<EVR<T>>(evalModel)) {}
  VisitAction operator()(Expr exp) {
    if (m_rw->preVisit(exp))
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    else
      return VisitAction::skipKids();
  }

  T getValue(Expr exp) { return m_rw->getValue(exp); }
};
} // namespace evalImpl
} // namespace eval
} // namespace expr

namespace expr {
namespace eval {

/**
 * Evaluate the given expression.
 *
 * Supported expressions:
 *  bit vectors, bools, lambdas, ite, arrays
 */
template <typename T> class Evaluate {
  EvalModel<T> *m_evalModel;

  template <typename A> A evaluateHelper(Expr exp) {
    evalImpl::EV<A> visitor(m_evalModel);

    visit(visitor, exp);
    return visitor.getValue(exp);
  }

public:
  Evaluate(EvalModel<T> *evalModel) : m_evalModel(evalModel) {}
  ~Evaluate() {}

  T evaluate(Expr exp) { return evaluateHelper<T>(exp); }
};
} // namespace eval
} // namespace expr
