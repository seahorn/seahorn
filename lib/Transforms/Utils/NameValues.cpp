/**
SeaHorn Verification Framework
Copyright (c) 2015 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified BSD license, please see license.txt for full
terms.

DM-0002198
*/

#define DEBUG_TYPE "name-values"

#include "ufo/Passes/NameValues.hpp"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/PassManager.h"

#include <boost/tokenizer.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include "avy/AvyDebug.h"

using namespace llvm;

namespace ufo
{
  char NameValues::ID = 0;
    
  bool NameValues::runOnModule (Module &M)
  {
    //avy::AvyEnableLog ("nv");
    
    for (Module::iterator FI = M.begin (), E = M.end (); FI != E; ++FI)
      runOnFunction (*FI);
    return false;
  }
    
  bool NameValues::runOnFunction (Function &F)
  {
    LOG ("nv", errs () << "Running on: " << F.getName () << "\n";);
    
    // -- print to string 
    std::string funcAsm;
    raw_string_ostream out (funcAsm);
    out << F;
    out.flush ();
      
    typedef boost::tokenizer<boost::char_separator<char> > tokenizer;
    boost::char_separator<char> nl_sep ("\n");
    boost::char_separator<char> sp_sep (" :\t%@");

    tokenizer lines (funcAsm, nl_sep);
    tokenizer::iterator line_iter = lines.begin ();

    // -- skip function attributes
    if (boost::starts_with(*line_iter, "; Function Attrs:"))
      ++line_iter;
     
    // -- skip function definition line
    ++line_iter;
     
    for (Function::iterator BI = F.begin (), BE = F.end (); 
	 BI != BE && line_iter != lines.end (); ++BI)
      {
	BasicBlock &BB = *BI;
	  
	if (!BB.hasName ())
	  {
	    std::string bb_line = *line_iter;
	    tokenizer names (bb_line, sp_sep);
	    std::string bb_name = *names.begin ();
            if (bb_name == ";") bb_name = "bb";
            LOG ("nv", errs () << "Found BB name: " << bb_name << "\n";);
            
	    BB.setName ("_" + bb_name);
	  }
	++line_iter;

	for (BasicBlock::iterator II = BB.begin (), IE = BB.end ();
	     II != IE && line_iter != lines.end (); ++II)
	  {
	    Instruction &I = *II;
            
	    if (!I.hasName () && !(I.getType ()->isVoidTy ())) 
	      {
		std::string inst_line = *line_iter;
                
		tokenizer names (inst_line, sp_sep);
		std::string inst_name = *names.begin ();
                LOG ("nv", 
                     errs () << "Found instruction name: " << inst_name << "\n");
            
		I.setName ("_" + inst_name);
	      }
            
	    ++line_iter;
	  }
      }
      
    return false;
  }    
  
}

static llvm::RegisterPass<ufo::NameValues> X ("name-values", "Names all unnamed values");
