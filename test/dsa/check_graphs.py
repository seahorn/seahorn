#!/usr/bin/env python

import os
import sys
import networkx as nx


def usage():
    print "Usage:\n\tcheck_graphs.py dotfile1 dotfile2 [both/nodes/edges]"
    return


def get_label(attrs):
    label = ''
    if 'label' in attrs:
        label = attrs['label']
    elif 0 in attrs and 'label' in attrs[0]:
        label = attrs[0]['label']
    return label


def comp_labels(attr1, attr2):
    return get_label(attr1) == get_label(attr2)


def isomorphic(DotFileName1, DotFileName2,
               CompareNodeLabels, CompareEdgeLabels):
    g1 = nx.drawing.nx_agraph.read_dot(DotFileName1)
    g2 = nx.drawing.nx_agraph.read_dot(DotFileName2)

    node_comp = comp_labels if CompareNodeLabels else None
    edge_comp = comp_labels if CompareEdgeLabels else None

    return nx.is_isomorphic(g1, g2,
                            node_match=node_comp, edge_match=edge_comp)


if __name__ == "__main__":

    if len(sys.argv) != 3 and len(sys.argv) != 4:
        usage()
        sys.exit()

    f1 = sys.argv[1]
    if not os.path.exists(f1):
        print "error: " + str(f1) + " does not exist"
        sys.exit()

    f2 = sys.argv[2]
    if not os.path.exists(f2):
        print "error: " + str(f2) + " does not exist"
        sys.exit()

    comp_node_lables = False
    comp_edge_labels = False
    if len(sys.argv) == 4:
        mode = sys.argv[3]
        if mode == 'both':
            comp_node_lables = comp_edge_labels = True
        elif mode == 'nodes':
            comp_node_lables = True
        elif mode == 'edges':
            comp_edge_labels = True
        else:
            usage()

    if isomorphic(f1, f2, comp_node_lables, comp_edge_labels):
        print "OK"
    else:
        print "KO"
