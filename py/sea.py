# SeaHorn Verification Framework
# Copyright (c) 2015 Carnegie Mellon University.
# All Rights Reserved.

# THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
# WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
# FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
# WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
# NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

# Released under a modified BSD license, please see license.txt for full
# terms.

# DM-0002198

import sys

def run_pp(args):
    print 'pp', args
def run_horn(args):
    print 'horn', args
def run_cc(args):
    pass

def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description = 'SeaHorn Verification Framework',
                          prog='sea')
    
    p.add_argument ('--cpu', type=int, dest='cpu', metavar='SEC',
                    help='CPU time limit (seconds)', default=-1)
    p.add_argument ('--mem', type=int, dest='mem', metavar='MB',
                    help='MEM limit (MB)', default=-1)
    p.add_argument ("--save-temps", dest="save_temps",
                       help="Do not delete temporary files",
                       action="store_true",
                       default=False)
    p.add_argument ("--temp-dir", dest="temp_dir", metavar='DIR',
                       help="Temporary directory",
                       default=None)

    sb = p.add_subparsers ()
    cc = sb.add_parser ('cc', help='compile')
    cc.set_defaults (func=run_cc)
    
    pp = sb.add_parser ('pp', help='pre-processor')
    pp.add_argument ('-o', '--output', dest='out_name', metavar='FILE',
                     help='Output file name')
    pp.add_argument ('--inline', dest='inline', help='Inline all functions',
                    default=False, action='store_true')
    pp.set_defaults (func=run_pp)
   
    horn = sb.add_parser ('horn', help='Horn solver')
    horn.set_defaults(func=run_horn)
    
    p.add_argument ('file', metavar='FILE', help='Input file')
    
    
    args = p.parse_args (argv)
    return args

def main (argv):
    args = parseArgs (argv[1:])
    args.func (args)
    return 0

if __name__ == '__main__':
    sys.exit (main (sys.argv))
