import sea

import os.path

from sea import add_in_out_args, which, createWorkDir

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

    def name_out_file (self, in_files, args=None, work_dir=None):
        assert (len (in_files) > 0)
        if len(in_files) == 1:
            in_file = in_files [0]
            if _bc_or_ll_file (in_file): return in_file
        else:
            in_file = 'merged.c'
        ext = '.bc'
        # if args.llvm_asm: ext = '.ll'
        return _remap_file_name (in_file, ext, work_dir)

    def run (self, args, extra):
        # do nothing on .bc and .ll files
        if _bc_or_ll_file (args.in_files[0]): return 0
        
        cmd_name = which (['clang-mp-3.6', 'clang-3.6', 'clang',
                                'clang-mp-3.5', 'clang-mp-3.4'])
        if cmd_name is None: raise IOError ('clang not found')
        self.clangCmd = sea.ExtCmd (cmd_name)

        argv = ['-c', '-emit-llvm', '-D__SEAHORN__', '-fgnu89-inline']

        argv.extend (filter (lambda s : s.startswith ('-D'), extra))

        if args.llvm_asm: argv.append ('-S')
        argv.append ('-m{0}'.format (args.machine))

        if args.debug_info: argv.append ('-g')
        
        
        if len(args.in_files) == 1:
            out_files = [args.out_file]
        else:
            # create private workdir
            workdir = createWorkDir ()
            out_files = [_remap_file_name (f, '.bc', workdir)
                         for f in args.in_files]
        
        for in_file, out_file in zip(args.in_files, out_files):
            if out_file is not None:
                argv.extend (['-o', out_file])

            # clone argv
            argv1 = list ()
            argv1.extend (argv)
            
            argv1.append (in_file)
            ret = self.clangCmd.run (args, argv1)
            if ret <> 0: return ret
            
        if len(out_files) > 1:
            # link
            cmd_name = which (['llvm-link-mp-3.6', 'llvm-link-3.6', 'llvm-link'])
            if cmd_name is None: raise IOError ('llvm-link not found')
            self.linkCmd = sea.ExtCmd (cmd_name)

            argv = []
            if args.llvm_asm: argv.append ('-S')
            if args.out_file is not None:
                argv.extend (['-o', args.out_file])
            argv.extend (out_files)
            return self.linkCmd.run (args, argv)
        
        return 0

    @property
    def stdout (self):
        return self.clangCmd.stdout

class Seapp(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(Seapp, self).__init__('pp', 'Pre-processing', allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        assert (len(in_files) == 1)
        ext = '.pp.bc'
        # if args.llvm_asm: ext = '.pp.ll'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seapp, self).mk_arg_parser (ap)
        ap.add_argument ('--inline', dest='inline', help='Inline all functions',
                         default=False, action='store_true')
        ap.add_argument ('--entry', dest='entry', help='Entry point if main does not exist',
                         default=None, metavar='FUNCTION')
        ap.add_argument ('--boc', dest='boc', help='Insert buffer overflow checks',
                         default=False, action='store_true')
        ap.add_argument ('--ioc', dest='ioc', help='Insert signed integer overflow checks',
                         default=False, action='store_true')
        ap.add_argument ('--externalize-addr-taken-functions',
                         help='Externalize uses of address-taken functions',
                         dest='enable_ext_funcs', default=False,
                         action='store_true')
        ap.add_argument ('--devirt-functions',
                         help='Devirtualize indirect functions',
                         dest='devirt_funcs', default=False,
                         action='store_true')
        ap.add_argument ('--no-kill-vaarg', help='Do not delete variadic functions',
                         dest='kill_vaarg', default=True, action='store_false')
        ap.add_argument ('--strip-extern', help='Replace external function calls ' + 
                         'by non-determinism', default=False, action='store_true',
                         dest='strip_external')
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

        if args.strip_external:
            argv.append ('--strip-extern=true')
        else:
            argv.append ('--strip-extern=false')

        if args.devirt_funcs:
            argv.append ('--devirt-functions')
            
        if args.enable_ext_funcs:
            argv.append ('--externalize-addr-taken-funcs')

        if args.boc:
            argv.append ('--boc')
            if args.inline:
                argv.append ('--boc-inline-all')
        if args.ioc:
            argv.append ('--ioc')
            if args.inline:
                argv.append ('--ioc-inline-all')
        if args.entry is not None:
            argv.append ('--entry-point=\"{0}\"'.format (args.entry))

        if args.kill_vaarg:
            argv.append('--kill-vaarg=true')
        else:
            argv.append('--kill-vaarg=false')
            
        if args.llvm_asm: argv.append ('-S')
        argv.extend (args.in_files)
        return self.seappCmd.run (args, argv)

class MixedSem(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(MixedSem, self).__init__('ms', 'Mixed semantics transformation',
                                       allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        ext = '.ms.bc'
        # if args.llvm_asm: ext = '.ms.ll'
        return _remap_file_name (in_files[0], ext, work_dir)

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
        argv.extend (args.in_files)
        return self.seappCmd.run (args, argv)

class CutLoops(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(CutLoops, self).__init__('cut-loops', 'Loop cutting transformation',
                                       allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        ext = '.cut.bc'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (CutLoops, self).mk_arg_parser (ap)
        ap.add_argument ('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name)

        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        argv.append ('--horn-cut-loops')
        if args.llvm_asm: argv.append ('-S')
        argv.extend (args.in_files)

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])

        return self.seappCmd.run (args, argv)

class Seaopt(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(Seaopt, self).__init__('opt', 'Compiler optimizations', allow_extra=True)

    @property
    def stdout (self):
        return self.seaoptCmd.stdout

    def name_out_file (self, in_files, args, work_dir=None):
        ext = '.o.bc'
        # ext = 'o{0}.bc'.format(args.opt_level)
        # if args.llvm_asm: ext = 'o{0}.ll'.format(args.opt_level)
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Seaopt, self).mk_arg_parser (ap)
        ap.add_argument ('-O', type=int, dest='opt_level', metavar='INT',
                         help='Optimization level L:[0,1,2,3]', default=3)
        ap.add_argument ('--enable-indvar', dest='enable_indvar', default=False,
                         action='store_true')
        ap.add_argument ('--enable-loop-idiom', dest='enable_loop_idiom', default=False,
                         action='store_true')
        ap.add_argument ('--enable-nondet-init', dest='enable_nondet_init', default=False,
                         action='store_true')
        ap.add_argument ('--llvm-inline-threshold', dest='inline_threshold',
                         type=int, metavar='T',
                         help='Inline threshold (default = 255)')
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
        if not args.enable_nondet_init:
            argv.append ('--enable-nondet-init=false')
        if args.inline_threshold is not None:
            argv.append ('--inline-threshold={t}'.format(t=args.inline_threshold))

        argv.extend (args.in_files)
        if args.llvm_asm: argv.append ('-S')
        return self.seaoptCmd.run (args, argv)

class Unroll(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(Unroll, self).__init__('unroll', 'Unroll loops', allow_extra=True)

    @property
    def stdout (self):
        return self.seaoptCmd.stdout

    def name_out_file (self, in_files, args, work_dir=None):
        ext = '.ul.bc'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Unroll, self).mk_arg_parser (ap)
        ap.add_argument ('--threshold', type=int, help='Unrolling threshhold. ' +
                         'Loops of larger size than this value will not ' +
                         'be unrolled (-unroll-threshold)',
                         default=131072, metavar='T')
        ap.add_argument ('--bound', default=0, type=int,
                         help='Unroll bound (-unroll-count)', metavar='B')
        ap.add_argument ('--enable-runtime', dest='enable_runtime',
                         default=False, action='store_true',
                         help='Allow unrolling loops with runtime trip count ' +
                         '(-unroll-runtime)')
        ap.add_argument ('--enable-partial', dest='enable_partial',
                         default=False, action='store_true',
                         help='Enable partial unrolling (-unroll-allow-partial)')
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

        # fake loops to be in the form suitable for loop-unroll
        argv.append ('-fake-latch-exit')
        
        argv.append ('-loop-unroll')
        if args.enable_runtime:
            argv.append ('-unroll-runtime')
        if args.enable_partial:
            argv.append ('-unroll-allow-partial')
        if args.bound > 0:
            argv.append ('-unroll-count={b}'.format(b=args.bound))
        argv.append ('-unroll-threshold={t}'.format(t=args.threshold))

        argv.extend (args.in_files)
        if args.llvm_asm: argv.append ('-S')
        return self.seaoptCmd.run (args, argv)    
    
def _is_seahorn_opt (x):
    if x.startswith ('-'):
        y = x.strip ('-')
        return y.startswith ('horn') or \
            y.startswith ('crab') or y.startswith ('log')
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

    def name_out_file (self, in_files, args=None, work_dir=None):
        return _remap_file_name (in_files[0], '.smt2', work_dir)

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
        ap.add_argument ('--show-invars',
                         help='Display computed invariants',
                         dest='show_invars', default=False, action='store_true')
        ## Begin Crab ##
        ap.add_argument ('--crab',
                         help='Enable Crab abstract interpreter',
                         dest='crab', default=False, action='store_true')
        ap.add_argument ('--crab-dom',
                         help='Choose Crab abstract domain',
                         choices=['int','ric','zones','term','num'],
                         dest='crab_dom', default='int')
        ap.add_argument ('--crab-track',
                         help='Track registers, pointers, and memory',
                         choices=['int', 'ptr', 'arr'], dest='crab_track', default='int')
        ap.add_argument ('--crab-inter',
                         help='Perform inter-procedural analysis',
                         dest='crab_inter', default=False, action='store_true')
        ## End Crab ##
        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seahornCmd = sea.ExtCmd (cmd_name)

        argv = list()

        if args.crab:
            argv.append ('--horn-crab')
            argv.append ('--crab-dom={0}'.format (args.crab_dom))
            argv.append ('--crab-track-lvl={0}'.format (args.crab_track))
            if args.crab_inter:
                argv.append ('--crab-inter')

        if args.solve or args.out_file is not None:
            argv.append ('--keep-shadows=true')
            
        if args.solve:
            argv.append ('--horn-solve')
            # Cannot delete shadows since they are used by the solver
            if args.show_invars:
                argv.append ('--horn-answer')
        if args.cex is not None and args.solve:
            argv.append ('-horn-cex')
            argv.append ('-horn-svcomp-cex={0}'.format (args.cex))
            #argv.extend (['-log', 'cex'])
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
        argv.extend (args.in_files)

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

    def name_out_file (self, in_files, args=None, work_dir=None):
        return _remap_file_name (in_files[0], '.clp', work_dir)

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
        argv.extend (args.in_files)

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

    def name_out_file (self, in_files, args, work_dir=None):
        ext = 'lfe.ll'
        assert (len (in_files) > 0)
        if len(in_files) > 1:
            in_file = 'merged.c'
        else:
            in_file = in_files[0]
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

        argv = ['--no-seahorn', '-o', args.out_file]
        argv.append ('-m{0}'.format (args.machine))
        if args.debug_info: argv.append ('--mark-lines')
        argv.extend (args.in_files)
        
        return self.lfeCmd.run (args, argv)

class Crab (sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (Crab, self).__init__ ('crab',
                                     'Instrument LLVM bitcode with invariants inferred by Crab',
                                     allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        ext = 'crab.ll'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (Crab, self).mk_arg_parser (ap)
        ap.add_argument ('--crab-dom',
                         help='Choose Crab abstract domain',
                         choices=['int','ric','zones','term','num'],
                         dest='crab_dom', default='int')
        ap.add_argument ('--crab-track',
                         help='Track registers, pointers, and memory',
                         choices=['int', 'ptr', 'arr'], dest='crab_track', default='int')
        ap.add_argument ('--crab-inter',
                         help='Perform inter-procedural analysis',
                         dest='crab_inter', default=False, action='store_true')
        # ap.add_argument ('--crab-add-at-entries',
        #                  help='Instrument code with invariants at each block entry',
        #                  dest='insert_entries', default=False, action='store_true')
        # ap.add_argument ('--crab-add-after-loads',
        #                  help='Instrument code with invariants after each load instruction',
        #                  dest='insert_loads', default=False, action='store_true')
        add_in_out_args (ap)

        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seappCmd = sea.ExtCmd (cmd_name)

        argv = list()
        argv.append ('--horn-crab')
        argv.append ('--crab-dom={0}'.format (args.crab_dom))
        argv.append ('--crab-track-lvl={0}'.format (args.crab_track))
        if args.crab_inter:
                argv.append ('--crab-inter')
        #if args.insert_entries:
        argv.append ('--crab-add-invariants-at-entries')
        #if args.insert_loads:
        argv.append ('--crab-add-invariants-after-loads')

        if args.out_file is not None: argv.extend (['-oll', args.out_file])
        argv.extend (args.in_files)
        return self.seappCmd.run (args, argv)


FrontEnd = sea.SeqCmd ('fe', 'Front end: alias for clang|pp|ms|opt',
                       [Clang(), Seapp(), MixedSem(), Seaopt ()])
Smt = sea.SeqCmd ('smt', 'alias for fe|horn', FrontEnd.cmds + [Seahorn()])
Clp = sea.SeqCmd ('clp', 'alias for fe|horn-clp', FrontEnd.cmds + [SeahornClp()])
Pf = sea.SeqCmd ('pf', 'alias for fe|horn --solve',
                 FrontEnd.cmds + [Seahorn(solve=True)])
LfeSmt = sea.SeqCmd ('lfe-smt', 'alias for lfe|horn', [LegacyFrontEnd(), Seahorn()])
LfeClp= sea.SeqCmd ('lfe-clp', 'alias for lfe|horn-clp', [LegacyFrontEnd(), SeahornClp()])
BndSmt = sea.SeqCmd ('bnd-smt', 'alias for fe|unroll|cut-loops|ms|opt|horn',
                     FrontEnd.cmds + [Unroll(), CutLoops(), MixedSem (),
                                      Seaopt(), Seahorn()])
Bpf = sea.SeqCmd ('bpf', 'alias for fe|unroll|cut-loops|opt|horn --solve',
                  FrontEnd.cmds + [Unroll(), CutLoops(), Seaopt(), Seahorn(solve=True)])
feCrab = sea.SeqCmd ('fe-crab', 'alias for fe|crab', FrontEnd.cmds + [Crab()])
