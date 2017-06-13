#include "llvm/Pass.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Support/DOTGraphTraits.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Analysis/DSA/DsaAnalysis.hh"
#include "seahorn/Analysis/DSA/Info.hh"
#include "seahorn/Analysis/DSA/GraphTraits.hh"

#include "avy/AvyDebug.h"

/*
   Convert each DSA graph to .dot file.
 */

static llvm::cl::opt<std::string>
OutputDir("mem-dot-outdir",
	  llvm::cl::desc("Output directory for dot files"),
	  llvm::cl::init(""),
	  llvm::cl::value_desc("DIR"));


namespace seahorn {

  /* XXX: The API of llvm::GraphWriter is not flexible enough.
     We need the labels for source and destinations of edges to be the
     same rather than s0,s1... and d0,d1,..

     seahorn::GraphWriter is a copy of llvm::GraphWriter but with
     some changes (search for MODIFICATION) in writeEdge customized to 
     output nice Dsa graphs.
  */
  
  template<typename GraphType>
  class GraphWriter {
    raw_ostream &O;
    const GraphType &G;
    
    typedef DOTGraphTraits<GraphType>           DOTTraits;
    typedef GraphTraits<GraphType>              GTraits;
    typedef typename GTraits::NodeType          NodeType;
    typedef typename GTraits::nodes_iterator    node_iterator;
    typedef typename GTraits::ChildIteratorType child_iterator;
    DOTTraits DTraits;
    
    // Writes the edge labels of the node to O and returns true if there are any
    // edge labels not equal to the empty string "".
    bool getEdgeSourceLabels(raw_ostream &O, NodeType *Node) {
      child_iterator EI = GTraits::child_begin(Node);
      child_iterator EE = GTraits::child_end(Node);
      bool hasEdgeSourceLabels = false;
    
      for (unsigned i = 0; EI != EE && i != 64; ++EI, ++i) {
	std::string label = DTraits.getEdgeSourceLabel(Node, EI);
	
	if (label.empty())
	  continue;

	hasEdgeSourceLabels = true;
	
	if (i)
	  O << "|";
	
	O << "<s" << i << ">" << DOT::EscapeString(label);
      }
      
      if (EI != EE && hasEdgeSourceLabels)
	O << "|<s64>truncated...";
    
      return hasEdgeSourceLabels;
    }
    
  public:
    GraphWriter(raw_ostream &o, const GraphType &g, bool SN) : O(o), G(g) {
      DTraits = DOTTraits(SN);
    }
    
    void writeGraph(const std::string &Title = "") {
      // Output the header for the graph...
      writeHeader(Title);
      
      // Emit all of the nodes in the graph...
      writeNodes();
      
      // Output any customizations on the graph
      DOTGraphTraits<GraphType>::addCustomGraphFeatures(G, *this);
      
      // Output the end of the graph
      writeFooter();
    }
    
    void writeHeader(const std::string &Title) {
      std::string GraphName = DTraits.getGraphName(G);
      
      if (!Title.empty())
	O << "digraph \"" << DOT::EscapeString(Title) << "\" {\n";
      else if (!GraphName.empty())
	O << "digraph \"" << DOT::EscapeString(GraphName) << "\" {\n";
      else
	O << "digraph unnamed {\n";
      
      if (DTraits.renderGraphFromBottomUp())
	O << "\trankdir=\"BT\";\n";
      
      if (!Title.empty())
	O << "\tlabel=\"" << DOT::EscapeString(Title) << "\";\n";
      else if (!GraphName.empty())
      O << "\tlabel=\"" << DOT::EscapeString(GraphName) << "\";\n";
      O << DTraits.getGraphProperties(G);
      O << "\n";
    }

    void writeFooter() {
      // Finish off the graph
      O << "}\n";
    }
    
    void writeNodes() {
      // Loop over the graph, printing it out...
      for (node_iterator I = GTraits::nodes_begin(G), E = GTraits::nodes_end(G);
	   I != E; ++I)
	if (!isNodeHidden(*I))
	  writeNode(*I);
    }

    bool isNodeHidden(NodeType &Node) {
      return isNodeHidden(&Node);
    }
    
    bool isNodeHidden(NodeType *const *Node) {
      return isNodeHidden(*Node);
    }
    
    bool isNodeHidden(NodeType *Node) {
      return DTraits.isNodeHidden(Node);
    }

    void writeNode(NodeType& Node) {
      writeNode(&Node);
    }
    
    void writeNode(NodeType *const *Node) {
      writeNode(*Node);
    }

    void writeNode(NodeType *Node) {
      std::string NodeAttributes = DTraits.getNodeAttributes(Node, G);
      
      O << "\tNode" << static_cast<const void*>(Node) << " [shape=record,";
      if (!NodeAttributes.empty()) O << NodeAttributes << ",";
      O << "label=\"{";
      
      if (!DTraits.renderGraphFromBottomUp()) {
	O << DOT::EscapeString(DTraits.getNodeLabel(Node, G));

	// If we should include the address of the node in the label, do so now.
	std::string Id = DTraits.getNodeIdentifierLabel(Node, G);
	if (!Id.empty())
	  O << "|" << DOT::EscapeString(Id);
	
	std::string NodeDesc = DTraits.getNodeDescription(Node, G);
	if (!NodeDesc.empty())
	  O << "|" << DOT::EscapeString(NodeDesc);
      }
      
      std::string edgeSourceLabels;
      raw_string_ostream EdgeSourceLabels(edgeSourceLabels);
      bool hasEdgeSourceLabels = getEdgeSourceLabels(EdgeSourceLabels, Node);
      
      if (hasEdgeSourceLabels) {
	if (!DTraits.renderGraphFromBottomUp()) O << "|";
	
	O << "{" << EdgeSourceLabels.str() << "}";
	
	if (DTraits.renderGraphFromBottomUp()) O << "|";
      }
      
      if (DTraits.renderGraphFromBottomUp()) {
	O << DOT::EscapeString(DTraits.getNodeLabel(Node, G));

	// If we should include the address of the node in the label, do so now.
	std::string Id = DTraits.getNodeIdentifierLabel(Node, G);
	if (!Id.empty())
	  O << "|" << DOT::EscapeString(Id);
	
	std::string NodeDesc = DTraits.getNodeDescription(Node, G);
	if (!NodeDesc.empty())
	  O << "|" << DOT::EscapeString(NodeDesc);	
      }

      #if 0 
      // XXX: MODIFICATION
      // if (DTraits.hasEdgeDestLabels()) {
      // 	O << "|{";
	
      // 	unsigned i = 0, e = DTraits.numEdgeDestLabels(Node);
      // 	for (; i != e && i != 64; ++i) {
      // 	  if (i) O << "|";
      // 	  O << "<d" << i << ">"
      // 	    << DOT::EscapeString(DTraits.getEdgeDestLabel(Node, i));
      // 	}
	
      // 	if (i != e)
      // 	  O << "|<d64>truncated...";
      // 	O << "}";
      // }
      #endif
      
      O << "}\"];\n";   // Finish printing the "node" line
      
      // Output all of the edges now
      child_iterator EI = GTraits::child_begin(Node);
      child_iterator EE = GTraits::child_end(Node);
      for (unsigned i = 0; EI != EE && i != 64; ++EI, ++i)
	if (!DTraits.isNodeHidden(*EI))
	  writeEdge(Node, i, EI);
      for (; EI != EE; ++EI)
	if (!DTraits.isNodeHidden(*EI))
	  writeEdge(Node, 64, EI);
    }
    
    void writeEdge(NodeType *Node, unsigned edgeidx, child_iterator EI) {
      if (NodeType *TargetNode = *EI) {
	int DestPort = -1;

	#if 0 
	// MODIFICATION
	// if (DTraits.edgeTargetsEdgeSource(Node, EI)) {
	//   child_iterator TargetIt = DTraits.getEdgeTarget(Node, EI);
	//   // Figure out which edge this targets...
	//   unsigned Offset =
	//     (unsigned)std::distance(GTraits::child_begin(TargetNode), TargetIt);
	//   DestPort = static_cast<int>(Offset);
	// }
	#else
	DestPort = DTraits.getIndex (TargetNode, EI.getOffset ());
	#endif
	
	if (DTraits.getEdgeSourceLabel(Node, EI).empty())
	  edgeidx = -1;

	emitEdge(static_cast<const void*>(Node), edgeidx,
		 static_cast<const void*>(TargetNode), DestPort,
		 DTraits.getEdgeAttributes(Node, EI, G));
      }
    }
    
    /// emitSimpleNode - Outputs a simple (non-record) node
    void emitSimpleNode(const void *ID, const std::string &Attr,
			const std::string &Label, unsigned NumEdgeSources = 0,
			const std::vector<std::string> *EdgeSourceLabels = nullptr) {
      O << "\tNode" << ID << "[ ";
      if (!Attr.empty())
	O << Attr << ",";
      O << " label =\"";
      if (NumEdgeSources) O << "{";
      O << DOT::EscapeString(Label);
      if (NumEdgeSources) {
	O << "|{";
	
	for (unsigned i = 0; i != NumEdgeSources; ++i) {
	  if (i) O << "|";
	  O << "<s" << i << ">";
	  if (EdgeSourceLabels) O << DOT::EscapeString((*EdgeSourceLabels)[i]);
	}
	O << "}}";
      }
      O << "\"];\n";
    }
    
    /// emitEdge - Output an edge from a simple node into the graph...
    void emitEdge(const void *SrcNodeID, int SrcNodePort,
		  const void *DestNodeID, int DestNodePort,
		  const std::string &Attrs) {
      if (SrcNodePort  > 64) return;             // Eminating from truncated part?
      if (DestNodePort > 64) DestNodePort = 64;  // Targeting the truncated part?
      
      O << "\tNode" << SrcNodeID;
      if (SrcNodePort >= 0)
	O << ":s" << SrcNodePort;
      O << " -> Node" << DestNodeID;

      // Edges that go to cells with zero offset do not
      // necessarily point to field 0. This makes graphs nicer.
      if (DestNodePort > 0 && DTraits.hasEdgeDestLabels()) {
      //if (DestNodePort >= 0 && DTraits.hasEdgeDestLabels()) {
	#if 0
	// MODIFICATION
	//O << ":d" << DestNodePort;
	#else
	O << ":s" << DestNodePort;
	#endif 
      }
      
      if (!Attrs.empty())
	O << "[" << Attrs << "]";
      O << ";\n";
    }
    
    /// getOStream - Get the raw output stream into the graph file. Useful to
    /// write fancy things using addCustomGraphFeatures().
    raw_ostream &getOStream() {
      return O;
    }
  };

  template<typename GraphType>
  raw_ostream &WriteGraph(raw_ostream &O, const GraphType &G,
			  bool ShortNames = false,
			  const Twine &Title = "") {
    // Start the graph emission process...
    GraphWriter<GraphType> W(O, G, ShortNames);
    
    // Emit the graph.
    W.writeGraph(Title.str());
    return O;
  }
  
}// end namspace seahorn

namespace llvm {

  template<>
  struct DOTGraphTraits<seahorn::dsa::Graph*> : public DefaultDOTGraphTraits {

    DOTGraphTraits (bool& b) {}    
    DOTGraphTraits () {}

    // static std::string getGraphName(const seahorn::dsa::Graph *G) {
    // }

    static std::string getGraphProperties(const seahorn::dsa::Graph *G) {
      std::string empty;
      raw_string_ostream OS(empty);
      OS << "\tgraph [center=true, ratio=true, bgcolor=lightgray, fontname=Helvetica];\n"; 
      OS << "\tnode  [fontname=Helvetica, fontsize=11];\n";
      return OS.str();
    }
    
    static std::string getNodeAttributes (const seahorn::dsa::Node *N,
                                          const seahorn::dsa::Graph *G){
      std::string empty;
      raw_string_ostream OS(empty);
      if (N->isCollapsed ()) {
	OS << "color=brown1, style=filled";
      }
      return OS.str();
    }     
    

    static std::string getNodeLabel(const seahorn::dsa::Node *N,
				    const seahorn::dsa::Graph *G) {
      std::string empty;
      raw_string_ostream OS(empty);
      if (N->isForwarding ()) {
	OS << "FORWARDING";
      } else {
	if (N->isCollapsed ())
	  OS << "COLLAPSED";
	else {
	  // Go through all the types, and just print them.
	  typedef typename seahorn::dsa::Node::types_type types_type_t;
	  
	  const types_type_t &ts = N->types ();
	  bool firstType = true;
	  OS << "{";
	  if (ts.begin() != ts.end()) {
	    for (typename types_type_t::const_iterator ii = ts.begin(),
		   ee = ts.end(); ii != ee; ++ii) {
	      if (!firstType) OS << ",";
	      firstType = false;
	      OS << ii->first << ":"; // offset
	      if (ii->second.begin () != ii->second.end()) {
		bool first = true;
		for (const Type * t: ii->second) {
		  if (!first) OS << "|";
		  t->print(OS);
		  first = false;
		}
	      }
	      else
		OS << "void";
	    }
	  }
	  else {
	    OS << "void";
	  }
	  OS << "}";
	}
	OS << ":";
	typename seahorn::dsa::Node::NodeType  node_type = N->getNodeType();
	if (node_type.array) OS << " Sequence ";
	if (node_type.alloca) OS << "S";
	if (node_type.heap) OS << "H";
	if (node_type.global) OS << "G";
	if (node_type.unknown) OS << "U";
	if (node_type.incomplete) OS << "I";
	if (node_type.modified) OS << "M";
	if (node_type.read) OS << "R";
	if (node_type.external) OS << "E";
	if (node_type.externFunc) OS << "X";
	if (node_type.externGlobal) OS << "Y";
	if (node_type.inttoptr) OS << "P";
	if (node_type.ptrtoint) OS << "2";
	if (node_type.vastart) OS << "V";
	if (node_type.dead) OS << "D";
	//OS << " " << N->size() << " ";
      }

      return OS.str();
    }

    bool isNodeHidden(seahorn::dsa::Node *Node) {
      // TODO: do not show nodes without incoming edges
      return false;
    }

    static std::string getEdgeSourceLabel(const seahorn::dsa::Node *Node,
                                          seahorn::dsa::Node::iterator I) {
      std::string S;
      llvm::raw_string_ostream O(S);
      O << I.getOffset();
      return O.str();
    }

    static bool hasEdgeDestLabels () { return true;}

    static unsigned numEdgeDestLabels (const seahorn::dsa::Node *Node) {
      return Node->links ().size();
    }
    
    ///////
    // XXX: if we use llvm::GraphWriter and we want to add destination labels.
    // It won't show the graphs as we want anyway.
    ///////
    // static std::string getEdgeDestLabel(const seahorn::dsa::Node *Node,
    // 					unsigned Idx) {
    //   std::string S;
    //   llvm::raw_string_ostream O(S);
    //   O << getOffset (Node,Idx);
    //   return O.str();
    // }

    // static bool edgeTargetsEdgeSource(const void *Node,
    // 				      seahorn::dsa::Node::iterator I) {
    //   if (I.getOffset() < I->getNode()->size()) {
    //   	if (I->hasLink (I.getOffset())) {
    // 	  //unsigned O = I->getLink(I.getOffset()).getOffset();
    // 	  //return O != 0;
    // 	  return true;
    // 	} else {
    // 	  return false;
    // 	}
    //   } else {
    //   	return false;
    //   }
    // }

    // static seahorn::dsa::Node::iterator getEdgeTarget(const seahorn::dsa::Node *Node,
    // 						      seahorn::dsa::Node::iterator I) {
    //   unsigned O = I->getLink(I.getOffset()).getOffset();
    //   unsigned LinkNo = O;
    //   seahorn::dsa::Node *N = *I;
    //   seahorn::dsa::Node::iterator R = N->begin();
    //   for (; LinkNo; --LinkNo) ++R;
    //   return R;
    // }

    // static int getOffset (const seahorn::dsa::Node *Node, unsigned Idx) {
    //   auto it = Node->links().begin();
    //   auto et = Node->links().end();
    //   unsigned i = 0;
    //   for (; it!=et; ++it,i++) {
    // 	if (i==Idx) {
    // 	  return it->first;
    // 	}
    //   }
    //   return -1;
    // }
    
    static int getIndex (const seahorn::dsa::Node *Node, unsigned Offset) {
      auto it = Node->links().begin();
      auto et = Node->links().end();
      unsigned idx = 0;
      for (; it!=et; ++it,++idx) {
    	if (it->first == Offset)
    	  return idx;
      }
      return -1;
    }
   
    static void addCustomGraphFeatures(seahorn::dsa::Graph *g,
				       seahorn::GraphWriter<seahorn::dsa::Graph*> &GW) {
      
      typedef seahorn::dsa::Graph::scalar_const_iterator scalar_const_iterator;
      typedef seahorn::dsa::Graph::formal_const_iterator formal_const_iterator;
      typedef seahorn::dsa::Graph::return_const_iterator return_const_iterator;      
      typedef seahorn::dsa::Graph Graph;
      typedef seahorn::dsa::Node Node;
      
      const Graph * G = g;

      // print edges from scalar (local and global) variables to cells
      { 
	scalar_const_iterator it = g->scalar_begin();
	scalar_const_iterator et = g->scalar_end();
	for (; it!=et; ++it) {
	  std::string OS_str;
	  llvm::raw_string_ostream OS(OS_str);
	  const llvm::Value* v = it->first;
	  if (v->hasName ())
	    OS << v->getName ();
	  else
	    OS << *v;
	  GW.emitSimpleNode(it->first, "shape=plaintext", OS.str());
	  Node *DestNode = it->second->getNode();
	  int EdgeDest = getIndex(DestNode, it->second->getOffset());
	  GW.emitEdge(it->first, -1,
		      DestNode, EdgeDest,
		      "arrowtail=tee,color=gray63");
		      
	}
      }

      // print edges from formal parameters to cells
      { 
	formal_const_iterator it = g->formal_begin();
	formal_const_iterator et = g->formal_end();
	for (; it!=et; ++it) {
	  std::string OS_str;
	  llvm::raw_string_ostream OS(OS_str);
	  const llvm::Argument* arg = it->first;
	  OS << arg->getParent()->getName () << "#" << arg->getArgNo();
	  GW.emitSimpleNode(it->first, "shape=plaintext,fontcolor=blue", OS.str());
	  Node *DestNode = it->second->getNode();
	  int EdgeDest = getIndex(DestNode, it->second->getOffset());
	  GW.emitEdge(it->first, -1,
		      DestNode, EdgeDest,
		      "tailclip=false,color=gray63");
		      
	}
      }

      // print edges from function return to cells
      { 
	return_const_iterator it = g->return_begin();
	return_const_iterator et = g->return_end();
	for (; it!=et; ++it) {
	  std::string OS_str;
	  llvm::raw_string_ostream OS(OS_str);
	  const llvm::Function* f = it->first;
	  OS << f->getName () << "#Ret";
	  GW.emitSimpleNode(it->first, "shape=plaintext,fontcolor=blue", OS.str());
	  Node *DestNode = it->second->getNode();
	  int EdgeDest = getIndex(DestNode, it->second->getOffset());
	  GW.emitEdge(it->first, -1,
		      DestNode, EdgeDest,
		      "arrowtail=tee,color=gray63");
		      
	}
      }
      
    }
  };

} // end namespace llvm

namespace seahorn {

  namespace dsa {

    using namespace llvm;

    static std::string appendOutDir (std::string FileName) {
      if (!OutputDir.empty ()) {
	if (!llvm::sys::fs::create_directory (OutputDir)) {
	  std::string FullFileName = OutputDir + "/" + FileName;
	  return FullFileName;
	}
      }
      return FileName;
    }
    
    static bool writeGraph (Graph *G, std::string Filename) {
      std::string FullFilename = appendOutDir (Filename);
      std::error_code EC;
      raw_fd_ostream File(FullFilename, EC, sys::fs::F_Text);
      if (!EC) {
	//llvm::WriteGraph(File, G);
	seahorn::WriteGraph(File, G);
	LOG("dsa-printer", G->write(errs()));
	return true;
      }
      return false;
    }
    
    struct DsaPrinter : public ModulePass {
      static char ID; 
      DsaAnalysis* m_dsa;
      
      DsaPrinter() : ModulePass(ID), m_dsa(nullptr) { }
      
      bool runOnModule(Module &M) override {
	m_dsa = &getAnalysis<dsa::DsaAnalysis>();
	if (m_dsa->getDsaAnalysis().kind () == CONTEXT_INSENSITIVE) {
	  Function *main = M.getFunction ("main");
	  if (main && m_dsa->getDsaAnalysis().hasGraph (*main)) {
	    Graph *G = &m_dsa->getDsaAnalysis().getGraph (*main);
	    std::string Filename = main->getName().str() + ".mem.dot";
	    writeGraph (G, Filename);
	  }
	} else {
	  for (auto &F: M) runOnFunction(F);
	}
	return false;
      }
      
      bool runOnFunction(Function &F) {
	if (m_dsa->getDsaAnalysis().hasGraph (F)) {	
	  Graph *G = &m_dsa->getDsaAnalysis().getGraph (F);
	  if (G->begin() != G->end()) {
	    std::string Filename = F.getName().str() + ".mem.dot";
	    writeGraph (G, Filename);
	  }
	}
	return false;
      }
      
      void getAnalysisUsage(AnalysisUsage &AU) const override {
	AU.setPreservesAll();
	AU.addRequired<DsaAnalysis> ();          
      }
      
    };
    
    struct DsaViewer : public ModulePass {
      static char ID;
      DsaAnalysis* m_dsa;
      const bool wait;
      
      DsaViewer() : ModulePass(ID), m_dsa(nullptr), wait(false) { }
      
      bool runOnModule(Module &M) override {
	m_dsa = &getAnalysis<dsa::DsaAnalysis>();
	if (m_dsa->getDsaAnalysis().kind () == CONTEXT_INSENSITIVE) {
	  Function *main = M.getFunction ("main");
	  if (main && m_dsa->getDsaAnalysis().hasGraph (*main)) {
	    Graph *G = &m_dsa->getDsaAnalysis().getGraph (*main);
	    std::string Filename = main->getName().str() + ".mem.dot";
	    if (writeGraph (G, Filename))
	      DisplayGraph(Filename, wait, GraphProgram::DOT);	      
	  }
	} else {
	  for (auto &F: M) runOnFunction(F);
	}
	return false;
      }
      
      bool runOnFunction(Function &F) {
	if (m_dsa->getDsaAnalysis().hasGraph (F)) {
	  Graph *G = &m_dsa->getDsaAnalysis().getGraph (F);
	  if (G->begin() != G->end()) {
	    std::string Filename = F.getName().str() + ".mem.dot";
	    if (writeGraph (G, Filename)) {
	      DisplayGraph(Filename, wait, GraphProgram::DOT);
	    }
	  }
	}
	return false;
      }
      
      void getAnalysisUsage(AnalysisUsage &AU) const override {
	AU.setPreservesAll();
	AU.addRequired<DsaAnalysis> ();          
      }
      
    };

    char DsaPrinter::ID = 0;    
    char DsaViewer::ID = 0;
    
  } // end namespace seahorn


  ModulePass *createDsaPrinterPass () {
    return new seahorn::dsa::DsaPrinter();
  }

  ModulePass *createDsaViewerPass () {
    return new seahorn::dsa::DsaViewer();
  }
  
} //end namespace seahorn

