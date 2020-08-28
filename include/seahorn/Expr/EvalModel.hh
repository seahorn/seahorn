#pragma once

#include "seahorn/Expr/EvalUtils.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprGmp.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpBinder.hh"

#include <math.h>
#include <stdlib.h>

namespace expr {
namespace eval {

/**
 * Bit vector structure. Holds the number(as type T) and its width
 *
 * \note bools are stored as 1/0 with a width of 1
 */
template <typename T> struct BvNum {
  T num = 0;
  unsigned width = 0;

  unsigned getWidth() const { return width; }

  /// \brief empty constructor
  BvNum() : num(0), width(0) {}

  /// \brief bool constructor.
  BvNum(bool a) : num(a), width(1) {}

  BvNum(T numArg, unsigned widthArg) : num(numArg), width(widthArg) {}

  bool operator<(const BvNum<T> &bnum) const { return num < bnum.num; }

  bool operator==(const BvNum<T> &bnum) const {
    return (num == bnum.num) && (getWidth() == bnum.getWidth());
  }
};

/**
 * Holds the data for an indivdual array.
 *
 * Maps indices of the array to their corresponding value.
 *
 * If there IS a default value, then it is assumed that every index not in the
 * map has the default value. If there is NOT a default value, then values
 * will need to be generated as needed
 *
 * In EvalModel, the array expressions are mapped to this struct
 *
 */
template <typename T> struct Arr {
  bool m_hasDefaultVal = false;
  BvNum<T> m_defaultVal;

  unsigned m_valWidth = 0; ///< used when generating new values

  std::map<BvNum<T>, BvNum<T>> m_map; ///< index, value

  Arr(BvNum<T> defaultVal)
      : m_hasDefaultVal(true), m_defaultVal(defaultVal),
        m_valWidth(defaultVal.getWidth()) {}
  Arr(unsigned valWidth) : m_hasDefaultVal(false), m_valWidth(valWidth) {}
};

/**
 * Holds the data for a lambda. Maps bound vars to their value
 *
 * The purpose of this is to keep bound vars within the scope of the individual
 * lambda.
 *
 * In EvalModel, lambda expressions are mapped to this struct
 *
 */
template <typename T> struct Lambda {
  std::map<Expr, BvNum<T>> m_map; ///< bound var, value
};

/**
 * \class EvalModel . The base class for the eval models
 *
 * \details The purpose is to generate and store values for constants, bound
 * variables, and arrays. All 3 types have their own get/set methods
 *
 * \note the get methods generate a value if one does not already exist
 *
 *  To create a new model, extend EvalModel, and override generateNum(). See
 *  EvalModelRand for an example
 */
template <typename Type> class EvalModel {

protected:
  /// maps the constants/bvars to their values
  std::map<Expr, BvNum<Type>> m_data;

  /// maps the base of the array struct that holds their data
  /// The base of the array is the inner most array expressions (array const,
  /// CONST_ARRAY)
  std::map<Expr, Arr<Type>> m_arrayData;

  /// maps lambdas to the struct that holds their data
  std::map<Expr, Lambda<Type>> m_lambdaData;

  /// create a number of the given width. To be overriden by derived classes
  virtual BvNum<Type> generateNum(unsigned width) = 0;

  BvNum<Type> generateBool() { return generateNum(1); }

  /// \brief generates a value for a bound variable
  /// \note supports BVSORT and BOOL bound vars
  BvNum<Type> generateBound(Expr exp) {
    Expr type = bind::rangeTy(exp);

    if (isOp<BVSORT>(type)) {
      unsigned width = bv::width(type);
      return generateNum(width);
    } else if (isOp<BOOL_TY>(type)) {
      return generateBool();
    } else {
      ERR << "Error: expected bvnum or bool bound var: " << *exp << "\n";
      assert(false);
    }

    return 0;
  }

  /// \brief generates a value for a constant
  /// \note supports BV consts and bool consts
  BvNum<Type> generateConst(Expr exp) {
    if (bv::isBvConst(exp)) {

      unsigned width = bv::widthBvConst(exp);

      return generateNum(width);
    } else if (bind::isBoolConst(exp)) {
      return generateBool();
    } else {
      ERR << "Error: expected bvnum or bool const: " << *exp << "\n";
      assert(false);
    }

    return 0;
  }

public:
  EvalModel() {}

  /// maps the given constnat to the given value
  void setConstantValue(Expr constant, BvNum<Type> value) {
    m_data[constant] = value; // overwrite if key already exists
  }

  /// \return the constant's value. A value is generated if it does not already
  /// have one
  BvNum<Type> getConstantValue(Expr constant) {
    assert(bind::IsConst()(exp));

    if (m_data.count(constant)) {
      return m_data.at(constant);
    }

    BvNum<Type> result;

    if (bind::IsConst()(constant)) {
      result = generateConst(constant);
    } else if (bind::isBVar(constant)) {
      result = generateBound(constant);
    } else {
      ERR << "Error: expected constant or bound variable: " << *constant
          << "\n";
      assert(false);
    }

    m_data.insert({constant, result});

    return result;
  }

  /// \param array the base of the array expression(array constant or
  /// CONST_ARRAY)
  /// \return the value at the given index. A value is generated if
  /// it does not already have one
  BvNum<Type> getArrayValue(Expr array, BvNum<Type> idx) {
    assert(m_arrayData.count(array)); // newArray() should be called first

    Arr<Type> &arr = m_arrayData.at(array);

    if (arr.m_map.count(idx)) {
      return arr.m_map.at(idx);
    } else if (arr.m_hasDefaultVal) {
      return arr.m_defaultVal;
    }

    // value does not exist yet, so generate it
    BvNum<Type> value = generateNum(arr.m_valWidth);
    arr.m_map.insert({idx, value});

    return value;
  }

  /// maps the index of the given array to the given value
  /// \param array the base array (array constant or CONST_ARRAY)
  /// \param idx index of the array that will have its value set
  /// \param value the value that the index should have
  void setArrayValue(Expr array, BvNum<Type> idx, BvNum<Type> value) {
    assert(m_arrayData.count(array)); // newArray() should be called first

    Arr<Type> &arr = m_arrayData.at(array);

    arr.m_map[idx] = value; // override existing value
  }

  /// create a new array
  /// \param  array should be an array constant
  void newArray(Expr array) {
    assert(bind::isArrayConst(array));

    Expr fdecl = array->first();
    Expr arrType = bind::rangeTy(fdecl);
    Expr valType = arrType->right();

    unsigned width = 0;

    if (isOp<BVSORT>(valType)) {
      width = bv::width(valType);
    } else if (isOp<BOOL_TY>(valType)) {
      width = 1;
    } else {
      assert(false);
    }

    m_arrayData.emplace(array, width);
  }

  /// create a new array
  /// \param array should be a CONST_ARRAY expression
  /// \param defaultVal the default array value (ie. second param of CONST_ARRAY
  /// exprsession)
  void newArray(Expr array, BvNum<Type> defaultVal) {
    assert(isOp<CONST_ARRAY>(array));
    m_arrayData.emplace(array, defaultVal);
  }

  /// \param lambda the lambda expression that the bound var is in the scope of
  /// \return the value of the boundVar. A value is generated if
  /// it does not already have one
  BvNum<Type> getBoundValue(Expr lambda, Expr boundVar) {
    assert(m_lambdaData.count(array)); // newLambda() should be called first

    Lambda<Type> &l = m_lambdaData.at(lambda);

    if (l.m_map.count(boundVar)) {
      return l.m_map.at(boundVar);
    }

    // value does not exist yet, so generate it
    BvNum<Type> value = generateBound(boundVar);
    l.m_map.insert({boundVar, value});

    return value;
  }

  /// gives the given bound var a new value
  /// \param lambda the lambda expression that the bound var is in the scope of
  /// \param boundVar the bound var that will have its value set
  /// \param value the value that the bound var should have
  void setBoundValue(Expr lambda, Expr boundVar, BvNum<Type> value) {
    assert(m_lambdaData.count(lambda)); // newLambda() should be called first

    Lambda<Type> &l = m_lambdaData.at(lambda);

    l.m_map[boundVar] = value; // override existing value
  }

  /// create a new lambda
  void newLambda(Expr lambda) {
    assert(isOp<LAMDBA>(lambda));
    Lambda<Type> l;
    m_lambdaData.insert({lambda, l});
  }
};

/**
 * \brief Eval model to generate numbers randomly
 */
template <typename T> class EvalModelRand : public EvalModel<T> {

  mpz_rand m_rand;

public:
  EvalModelRand(unsigned seed = time(nullptr)) : m_rand(seed) { srand(seed); }

  ~EvalModelRand() = default;

  /// \brief creates a random number of the given width
  BvNum<T> generateNum(unsigned width) override {
    T num = evalUtils::zeroUpperBits<T>(rand(), width);
    return BvNum<T>(num, width);
  }
};

template <>
BvNum<mpz_class> EvalModelRand<mpz_class>::generateNum(unsigned width) {
  mpz_class num = m_rand.urandomb(width);

  return BvNum<mpz_class>(num, width);
}
} // namespace eval
} // namespace expr