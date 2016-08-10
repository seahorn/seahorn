add_llvm_library (SeaDsaAnalysis
  Graph.cc
  DsaLocal.cc
  DsaGlobal.cc
  DsaCallSite.cc
  Cloner.cc
  DsaInfo.cc
  Mapper.cc
  DsaBottomUp.cc
  DsaCallGraph.cc
  )

## DsaInfo requires NameValues 
target_link_libraries (SeaDsaAnalysis SeaTransformsUtils)