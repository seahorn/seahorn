#!/usr/bin/env python

import os
import sys
import networkx as nx

def usage ():
   print "check_graphs.py dotfile1 dotfile2 [both/nodes/edges]"
   return


def comp_labels (attr1, attr2):
   if 'label' not in attr1:
      return 'label' not in attr2
   return attr1['label'] == attr2['label']


def isomorphic (DotFileName1, DotFileName2,
                CompareNodeLabels, CompareEdgeLabels):
   g1 = nx.drawing.nx_agraph.read_dot(DotFileName1)
   g2 = nx.drawing.nx_agraph.read_dot(DotFileName2)

   return nx.is_isomorphic(g1, g2, comp_labels if CompareNodeLabels else None,
                           comp_labels if CompareEdgeLabels else None)

if __name__ == "__main__":

   if len(sys.argv) != 3 and len(sys.argv) != 4:
      usage ()
      sys.exit()

   f1 = sys.argv[1]
   if not os.path.exists (f1):
      print "error: " + str(f1) + " does not exist"
      sys.exit()

   f2 = sys.argv[2]
   if not os.path.exists (f2):
      print "error: " + str(f2) + " does not exist"
      sys.exit()

   comp_node_lables = False
   comp_edge_labels = False
   if len (sys.argv) == 4:
      mode = sys.argv[3]
      if mode == 'both':
         comp_node_lables = comp_edge_labels = True
      elif mode == 'nodes':
         comp_node_lables = True
      elif mode == 'edges':
         comp_edge_labels = True
      else:
         usage()

   if isomorphic (f1, f2, comp_node_lables, comp_edge_labels):
      print "OK"
   else:
      print "KO"
      
