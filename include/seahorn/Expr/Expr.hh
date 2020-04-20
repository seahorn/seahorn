#pragma once

#include <typeinfo>

#include <algorithm>
#include <array>
#include <deque>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <seahorn/Expr/ExprGmp.hh>

#include <boost/container/flat_set.hpp>
#include <boost/functional/hash_fwd.hpp>
#include <boost/intrusive_ptr.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/pool/pool.hpp>
#include <boost/pool/poolfwd.hpp>

#define BOOST_DISABLE_ASSERTS 1
// boost/ptr_vector.hpp has BOOST_ASSERT that rely on rtti
#include <boost/ptr_container/ptr_vector.hpp>
#undef BOOST_DISABLE_ASSERTS

#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Support/Casting.h"

#define mk_it_range llvm::make_range

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"

#include "seahorn/Expr/ExprApi.hh"

#include "seahorn/Expr/ExprOpBool.hh"

#include "seahorn/Expr/ExprOpArray.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpCompare.hh"
#include "seahorn/Expr/ExprOpGate.hh"
#include "seahorn/Expr/ExprOpNum.hh"
#include "seahorn/Expr/ExprOpSort.hh"
#include "seahorn/Expr/ExprOpStruct.hh"
#include "seahorn/Expr/ExprOpVariant.hh"

#include "seahorn/Expr/ExprOpBv.hh"

#include "seahorn/Expr/ExprOpMisc.hh"

namespace expr {
namespace op {}
/** Size of an expression as a DAG */
size_t dagSize(Expr e);
size_t dagSize(const ExprVector &vec);
/** Size of an expression as a tree */
size_t treeSize(Expr e);

// -- replace all occurrences of s by t
Expr replaceAll(Expr exp, Expr s, Expr t);
/** Replace all occurrences of s by t while simplifying the result */
Expr replaceAllSimplify(Expr exp, Expr s, Expr t);
/** Returns true if e1 contains e2 as a sub-expression */
bool contains(Expr e1, Expr e2);
} // namespace expr
