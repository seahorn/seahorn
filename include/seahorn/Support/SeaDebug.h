#ifndef __SEA__DEBUG__HPP_
#define __SEA__DEBUG__HPP_
#include "SeaAssert.h"
#include <set>
#include <string>

namespace seahorn {
// Exprs with dags smaller than this value with be dumped during logging
#define DAG_PRINT_LIMIT 64

#define DOG(CODE) LOG(DEBUG_TYPE, CODE)
#ifndef NSEALOG
#define LOG(TAG, CODE)                                                         \
  do {                                                                         \
    if (::seahorn::SeaLogFlag && ::seahorn::SeaLog.count(TAG) > 0) {           \
      CODE;                                                                    \
    }                                                                          \
  } while (0)

extern bool SeaLogFlag;
extern std::set<std::string> SeaLog;

void SeaEnableLog(std::string x);
#else
#define SeaEnableLog(X)
#define LOG(TAG, CODE)                                                         \
  do {                                                                         \
  } while (0)
#endif
} // namespace seahorn

#endif
