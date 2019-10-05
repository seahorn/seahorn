#ifndef __EXPR__SEAHORN__HH_
#define __EXPR__SEAHORN__HH_

/**
 * Seahorn extensions to the Expr library
 */

#include "seahorn/Expr/Expr.hh"

#include <boost/functional/hash.hpp>

#include "llvm/Support/raw_ostream.h"
#include <boost/lexical_cast.hpp>

#include "seahorn/Analysis/CutPointGraph.hh"

namespace expr
{
  using namespace seahorn;
  using namespace llvm;
  
  template<> struct TerminalTrait<const CutPoint*>
  {
    template <typename Stream>
    static void print (Stream &OS, const CutPoint *cp, int depth, bool brkt)
    {OS << "CP_" << cp->bb ().getName ().str ();}
    
    static bool less (const CutPoint *cp1, const CutPoint* cp2) 
    {return cp1 < cp2;}
    
    static bool equal_to (const CutPoint *cp1, const CutPoint *cp2)
    {return cp1 == cp2;}
    
    static size_t hash (const CutPoint *cp)
    {
      boost::hash<const CutPoint*> hasher;
      return hasher (cp);
    }
  };
}

namespace seahorn
{
  typedef expr::Terminal<const seahorn::CutPoint*> CP;
}



#endif
