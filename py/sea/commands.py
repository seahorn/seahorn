import sea 

import os.path

from sea import add_in_out_args, which

# remaps a file based on working dir and a new extension
def _remap_file_name (in_file, ext, work_dir):
    out_file = in_file
    if work_dir is not None:
        out_file = os.path.basename (in_file)
        out_file = os.path.join (work_dir, out_file)
    out_file = os.path.splitext (out_file)[0]
    out_file = out_file + ext
    return out_file


def _add_S_arg (ap):
    ap.add_argument ('-S', dest='llvm_asm', default=False, action='store_true',
                     help='Write output as LLVM assembly')
    return ap

def _bc_or_ll_file (name):
    ext = os.path.splitext (name)[1]
    return ext == '.bc' or ext == '.ll'
    
class Clang(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (Clang, self).__init__('clang', 'Compile', allow_extra=True)
        self.clangCmd = None

    def mk_arg_parser (self, ap):
        ap = super (Clang, self).mk_arg_parser (ap)
        ap.add_argument ('-m', type=int, dest='machine',
                         help='Machine architecture MACHINE:[32,64]', default=32)
        ap.add_argument ('-g', default=False, action='store_true',
                         dest='debug_info', help='Compile with debug info')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def name_out_file (self, in_file, args=None, work_dir=None):
        if _bc_or_ll_file (in_file): return in_file
        ext = '.bc'
        # if args.llvm_asm: ext = '.ll'
        return _remap_file_name (in_file, ext, work_dir)
        
    def run (self, args, extra):
        # do nothing on .bc and .ll files
        if _bc_or_ll_file (args.in_file): return 0

        cmd_name = which (['clang-mp-3.6', 'clang-3.6', 'clang',
                                'clang-mp-3.5', 'clang-mp-3.4'])
        if cmd_name is None: raise IOError ('clang not found')
        self.clangCmd = sea.ExtCmd (cmd_name)
        
        argv = ['-c', '-emit-llvm', '-D__SEAHORN__']

        argv.extend (filter (lambda s : s.startswith ('-D'), extra))
        
        if args.llvm_asm: argv.append ('-S')
        argv.append ('-m{0}'.format (args.machine))
        
        if args.debug_info: argv.append ('-g')
        if args.out_file is not None:
            argv.extend (['-o', args.out_file])
        argv.append (args.in_file)
        return self.clangCmd.run (args, argv)

    @property
    def stdout (self):
        return self.clangCmd.stdout

class Seapp(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(Seapp, self).__init__('pp', 'Pre-processing', allow_extra=True)
        
    @property
    def stdout (self):
        return self.seappCmd.stdout
        
    def name_out_file (self, in_file, args=None, work_dir=None):
        ext = '.pp.bc'
        # if args.llvm_asm: ext = '.pp.ll'
        return _remap_file_name (in_file, ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seapp, self).mk_arg_parser (ap)
        ap.add_argument ('--inline', dest='inline', help='Inline all functions',
                         default=False, action='store_true')
        ap.add_argument ('--boc', dest='boc', help='Insert buffer overflow checks',
                         default=False, action='store_true')
        ap.add_argument ('--ioc', dest='ioc', help='Insert signed integer overflow checks',
                         default=False, action='store_true')
        # ap.add_argument ('--entry', dest='entry', help='Entry point if main does not exist',
        #                  default=None, metavar='FUNCTION')

        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name)
        
        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if args.inline: argv.append ('--horn-inline-all')
        if args.boc:
            if args.inline:
                argv.append ('--boc-inline-all')
            else:
                argv.append ('--boc')
        if args.ioc:
            if args.inline:
                argv.append ('--ioc-inline-all')
            else:
                argv.append ('--ioc')
        # if args.entry is not None:
        #         argv.append ('--entry-point=\"{0}\"'.format (args.entry))

        if args.llvm_asm: argv.append ('-S')
        argv.append (args.in_file)
        return self.seappCmd.run (args, argv)
        
class MixedSem(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(MixedSem, self).__init__('ms', 'Mixed semantics transformation',
                                       allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout
        
    def name_out_file (self, in_file, args=None, work_dir=None):
        ext = '.ms.bc'
        # if args.llvm_asm: ext = '.ms.ll'
        return _remap_file_name (in_file, ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (MixedSem, self).mk_arg_parser (ap)
        ap.add_argument ('--no-ms', dest='ms_skip', help='Skip mixed semantics',
                         default=False, action='store_true')
        ap.add_argument ('--no-reduce-main', dest='reduce_main',
                         help='Do not reduce main to return paths only',
                         default=True, action='store_false')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name)
        
        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if not args.ms_skip: argv.append ('--horn-mixed-sem')
        if args.reduce_main: argv.append ('--ms-reduce-main')
        if args.llvm_asm: argv.append ('-S')
        argv.append (args.in_file)
        return self.seappCmd.run (args, argv)

class Seaopt(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(Seaopt, self).__init__('opt', 'Compiler optimizations', allow_extra=True)

    @property
    def stdout (self):
        return self.seaoptCmd.stdout
        
    def name_out_file (self, in_file, args, work_dir=None):
        ext = '.o.bc'
        # ext = 'o{0}.bc'.format(args.opt_level)
        # if args.llvm_asm: ext = 'o{0}.ll'.format(args.opt_level)
        return _remap_file_name (in_file, ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seaopt, self).mk_arg_parser (ap)
        ap.add_argument ('-O', type=int, dest='opt_level', metavar='INT',
                         help='Optimization level L:[0,1,2,3]', default=3)
        ap.add_argument ('--enable-indvar', dest='enable_indvar', default=False,
                         action='store_true')
        ap.add_argument ('--enable-loop-idiom', dest='enable_loop_idiom', default=False,
                         action='store_true')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap
    
    def run (self, args, extra):
        cmd_name = which (['seaopt', 'opt-mp-3.6', 'opt-3.6', 'opt'])
        if cmd_name is None: raise IOError ('neither seaopt nor opt where found')
        self.seaoptCmd = sea.ExtCmd (cmd_name)

        argv = ['-f', '-funit-at-a-time']
        if args.out_file is not None:
            argv.extend (['-o', args.out_file])
        if args.opt_level > 0 and args.opt_level <= 3:
            argv.append('-O{0}'.format (args.opt_level))
            
        if not args.enable_indvar:
            argv.append ('--enable-indvar=false')
        if not args.enable_loop_idiom:
            argv.append ('--enable-loop-idiom=false')
            
        argv.append (args.in_file)
        if args.llvm_asm: argv.append ('-S')
        return self.seaoptCmd.run (args, argv)

def _is_seahorn_opt (x):
    if x.startswith ('-'):
        y = x.strip ('-')
        return y.startswith ('horn') or \
            y.startswith ('ikos') or y.startswith ('log')
    return False

class Seahorn(sea.LimitedCmd):
    def __init__ (self, solve=False, quiet=False):
        super (Seahorn, self).__init__ ('horn', 'Generate (and solve) ' +
                                        'Constrained Horn Clauses in SMT-LIB format',
                                        allow_extra=True)
        self.solve = solve
        
    @property
    def stdout (self):
        return self.seahornCmd.stdout

    def name_out_file (self, in_file, args=None, work_dir=None):
        return _remap_file_name (in_file, '.smt2', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seahorn, self).mk_arg_parser (ap)
        add_in_out_args (ap)
        ap.add_argument ('--cex', dest='cex', help='Destination for a cex',
                         default=None, metavar='FILE')
        ap.add_argument ('--solve', dest='solve', action='store_true',
                         help='Solve', default=self.solve)
        ap.add_argument ('--ztrace', dest='ztrace', metavar='STR',
                         default=None, help='Z3 trace levels')
        ap.add_argument ('--verbose', '-v', dest='verbose', type=int, default=0,
                         help='Verbosity level', metavar='N')
        ap.add_argument ('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        ap.add_argument ('--oll', dest='asm_out_file', default=None,
                         help='LLVM assembly output file')
        ap.add_argument ('--step',
                         help='Step to use for encoding',
                         choices=['small', 'large', 'fsmall', 'flarge'],
                         dest='step', default='large')
        ap.add_argument ('--track',
                         help='Track registers, pointers, and memory',
                         choices=['reg', 'ptr', 'mem'], default='mem')
        ap.add_argument ('--ikos',
                         help='Enable IKOS abstract interpreter',
                         dest='ikos', default=False, action='store_true')
        ap.add_argument ('--show-invars',
                         help='Display computed invariants',
                         dest='show_invars', default=False, action='store_true')
                         
                         
        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seahornCmd = sea.ExtCmd (cmd_name)
        
        argv = list()
        if args.solve:
            argv.append ('--horn-solve')
            if args.ikos:
                argv.append ('--horn-ikos')
            if args.show_invars:
                argv.append ('--horn-answer')
        if args.cex is not None and args.solve:
            argv.append ('-horn-cex')
            argv.append ('-horn-svcomp-cex={0}'.format (args.cex))
            argv.extend (['-log', 'cex'])
        if args.asm_out_file is not None: argv.extend (['-oll', args.asm_out_file])
        
        argv.extend (['-horn-inter-proc',
                      '-horn-sem-lvl={0}'.format (args.track),
                      '--horn-step={0}'.format (args.step)])
        
        if args.verbose > 0: argv.extend (['-zverbose', str(args.verbose)])

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        if args.ztrace is not None:
            for l in args.ztrace.split (':'): argv.extend (['-ztrace', l])
        
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        argv.append (args.in_file)

        # pick out extra seahorn options
        argv.extend (filter (_is_seahorn_opt, extra))
        
            
        return self.seahornCmd.run (args, argv)
    
class SeahornClp(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (SeahornClp, self).__init__ ('horn-clp', allow_extra=True)
        self.help = 'Generate Constrained Horn Clauses in CLP format'
        
    @property
    def stdout (self):
        return self.seahornCmd.stdout

    def name_out_file (self, in_file, args=None, work_dir=None):
        return _remap_file_name (in_file, '.clp', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (SeahornClp, self).mk_arg_parser (ap)
        add_in_out_args (ap)
        ap.add_argument ('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        ap.add_argument ('--oll', dest='asm_out_file', default=None,
                         help='LLVM assembly output file')
        ap.add_argument ('--step',
                         help='Step to use for encoding',
                         choices=['clpsmall', 'clpfsmall'],
                         dest='step', default='clpsmall')
        ap.add_argument ('--clp-fapp',
                         default=False, action='store_true',
                         help='Print function applications in CLP format',
                         dest='clp_fapp')

        ### TODO: expose options for semantic level, inter-procedural
        ### encoding, step, flat, etc.
        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seahornCmd = sea.ExtCmd (cmd_name)
        
        argv = list()
        if args.asm_out_file is not None: argv.extend (['-oll', args.asm_out_file])
        
        argv.extend (['-horn-inter-proc',
                      '-horn-format=clp', '-horn-sem-lvl=reg', 
                      '--horn-step={0}'.format (args.step)])

        if args.clp_fapp:
            argv.extend (['--horn-clp-fapp'])

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        argv.append (args.in_file)

        # pick out extra seahorn options
        argv.extend (filter (_is_seahorn_opt, extra))
        
            
        return self.seahornCmd.run (args, argv)
    
class LegacyFrontEnd (sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (LegacyFrontEnd, self).__init__ ('lfe', allow_extra=True)
        self.help = "Legacy front-end (used in SV-COMP'15)"

    @property
    def stdout (self):
        return self.lfeCmd.stdout

    def name_out_file (self, in_file, args, work_dir=None):
        ext = 'lfe.ll'
        return _remap_file_name (in_file, ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (LegacyFrontEnd, self).mk_arg_parser (ap)
        ap.add_argument ('-m', type=int, dest='machine',
                         help='Machine architecture MACHINE:[32,64]', 
                         default=32)
        ap.add_argument ('-g', default=False, action='store_true',
                         dest='debug_info', help='Compile with debug info')
        add_in_out_args (ap)
        return ap

    def run (self, args, extra):
        import sys
        cmd_name = os.path.join (os.path.dirname (sys.argv[0]), 
                                 '..', 'legacy', 'bin', 'seahorn.py')
        if not sea.isexec (cmd_name):
            print 'No legacy front-end found at:', cmd_name
	    print 'Download from https://bitbucket.org/arieg/seahorn-gh/downloads/seahorn-svcomp15-r1.tar.bz2 (64bit) or https://bitbucket.org/arieg/seahorn-gh/downloads/lfe32-2015.tar.bz2 (32bit) and extract into `legacy` sub-directory'
            print 'Only supported on Linux'
            return 1

        import subprocess
        self.lfeCmd = sea.ExtCmd (cmd_name)

        argv = ['--no-seahorn', args.in_file, '-o', args.out_file]
        argv.append ('-m{0}'.format (args.machine))
        if args.debug_info: argv.append ('--mark-lines')

        return self.lfeCmd.run (args, argv)

FrontEnd = sea.SeqCmd ('fe', 'Front end: alias for clang|pp|ms|opt',
                       [Clang(), Seapp(), MixedSem(), Seaopt ()])
Smt = sea.SeqCmd ('smt', 'alias for fe|horn', FrontEnd.cmds + [Seahorn()])
Clp = sea.SeqCmd ('clp', 'alias for fe|horn-clp', FrontEnd.cmds + [SeahornClp()])
Pf = sea.SeqCmd ('pf', 'alias for fe|horn --solve',
                 FrontEnd.cmds + [Seahorn(solve=True)])
LfeSmt = sea.SeqCmd ('lfe-smt', 'alias for lfe|horn', [LegacyFrontEnd(), Seahorn()])
LfeClp= sea.SeqCmd ('lfe-clp', 'alias for lfe|horn-clp', [LegacyFrontEnd(), SeahornClp()])

