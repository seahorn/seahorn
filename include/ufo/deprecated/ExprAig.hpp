#ifndef _EXPR_AIG__HPP_
#define _EXPR_AIG__HPP_
#include "Expr.hpp"

/** a basic simplifier */

namespace expr
{
  namespace op
  {
    namespace boolop
    {
      /// aig-fy an expression and simplify it
      Expr aig (Expr e, bool gather = false);
      
      /// same as aig(e, true)
      inline Expr flat_aig (Expr e) { return aig (e, true); }

      /// size as number of gates + number of inputs
      unsigned aigSize (Expr e);
    }  
  }
}


#endif
