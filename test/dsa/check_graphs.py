#!/usr/bin/python

import os
import sys
import networkx as nx

def usage ():
   print "check_graphs.py dotfile1 dotfile2"
   return

def isomorphic (DotFileName1, DotFileName2):
   g1 = nx.drawing.nx_agraph.read_dot(DotFileName1)
   g2 = nx.drawing.nx_agraph.read_dot(DotFileName2)
   return nx.is_isomorphic(g1,g2)

if __name__ == "__main__":
   
   if len(sys.argv) != 3:
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

   if isomorphic (f1,f2):
      print "OK"
   else:
      print "KO"
      
