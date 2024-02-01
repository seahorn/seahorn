#pragma once

#include <iostream>
#include <string>
#include <unordered_map>

// Using X-Macro code pattern.
// Define the list of errors
#define TYERROR_LIST                                                           \
  X(TYERR0, "Ok.")                                                             \
  X(TYERR1, "Fapp: Rator and rand types do not match.")                        \
  X(TYERR2, "Fapp: Rator and rand arities do not match.")                      \
  X(TYERR3, "Fapp: Rator should be a function.")                               \
  X(TYERR4, "Expression is not well-formed.")

// ... add more errors here

// Define X-macro for generating the enum
enum g_TyErrorCode {
#define X(a, b) a,
  TYERROR_LIST
#undef X
};

// Declare the map
// static std::unordered_map<g_TyErrorCode, std::string> g_TyErrorMap;

// Define X-macro for populating the map
static std::unordered_map<g_TyErrorCode, std::string> g_TyErrorMap = {
#define X(a, b) {a, b},
    TYERROR_LIST
#undef X
};

// Macro to get error string
#define GET_ERROR_STR(ERROR_CODE) (g_TyErrorMap[ERROR_CODE])
