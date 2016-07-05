#include "seahorn/Analysis/DSA/Cloner.hh"

using namespace seahorn;
using namespace seahorn::dsa;

Node &Cloner::clone (const Node &n)
{
  // -- don't clone nodes that are already in the graph
  if (n.getGraph() == &m_graph) return *const_cast<Node*> (&n);
  
  // check the cache
  auto it = m_map.find (&n);
  if (it != m_map.end ())
    return *(it->second);

  // -- clone the node (except for the links)
  Node &nNode = m_graph.cloneNode (n);
  
  // -- update cache
  m_map.insert (std::make_pair (&n, &nNode));

  for (auto &kv : n.links ())
  {
    // dummy link (should not happen)
    if (kv.second->isNull ()) continue;
    
    // recursively clone the node pointed by the link 
    Cell nCell (&clone (*kv.second->getNode ()), kv.second->getOffset ());
    // create new link
    nNode.setLink (kv.first, nCell);
  }
  
  // -- don't expect the new node to collapse
  assert (!nNode.isForwarding ());
 
  return nNode;
}
