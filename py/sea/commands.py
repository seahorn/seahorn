import sea

import os.path
import sys
import shutil

from sea import add_in_out_args, add_tmp_dir_args, which, createWorkDir

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
    def __init__ (self, quiet=False, plusplus=False):
        super (Clang, self).__init__('clang', 'Compile', allow_extra=True)
        self.clangCmd = None
        self.plusplus = plusplus

    def mk_arg_parser (self, ap):
        ap = super (Clang, self).mk_arg_parser (ap)
        ap.add_argument ('-m', type=int, dest='machine',
                         help='Machine architecture MACHINE:[32,64]', default=32)
        ap.add_argument ('-g', default=False, action='store_true',
                         dest='debug_info', help='Compile with debug info')
        ap.add_argument ('-I', default=None,
                         dest='include_dir', help='Include')
        add_tmp_dir_args (ap)
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
        out_files = []
        if len(args.in_files) == 1:
            out_files.append (args.out_file)
        else:
            # create private workdir
            workdir = createWorkDir ()
            for f in args.in_files:
                if _bc_or_ll_file (f):
                    out_files.append(f)
                else:
                    out_files.append(_remap_file_name (f, '.bc', workdir))
        # do nothing on .bc and .ll files
        if _bc_or_ll_file (args.in_files[0]): return 0

        if self.plusplus:
            cmd_name = which (['clang++-mp-3.6', 'clang++-3.6', 'clang++',
                               'clang++-mp-3.5', 'clang++-mp-3.4'])
        else:
            cmd_name = which (['clang-mp-3.6', 'clang-3.6', 'clang',
                               'clang-mp-3.5', 'clang-mp-3.4'])
            
        if cmd_name is None: raise IOError ('clang not found')
        self.clangCmd = sea.ExtCmd (cmd_name)

        if not all (_bc_or_ll_file (f) for f  in args.in_files): 
            cmd_name = which (['clang-mp-3.6', 'clang-3.6', 'clang',
                               'clang-mp-3.5', 'clang-mp-3.4'])
            if cmd_name is None: raise IOError ('clang not found')
            self.clangCmd = sea.ExtCmd (cmd_name)

            argv = ['-c', '-emit-llvm', '-D__SEAHORN__', '-fgnu89-inline']

            argv.extend (filter (lambda s : s.startswith ('-D'), extra))

            if args.llvm_asm: argv.append ('-S')
            argv.append ('-m{0}'.format (args.machine))
            
            if args.include_dir is not None:
                argv.append ('-I' + args.include_dir)

            include_dir = os.path.dirname (sys.argv[0])
            include_dir = os.path.dirname (include_dir)
            include_dir = os.path.join (include_dir, 'include')
            argv.append ('-I' + include_dir)

            if args.debug_info: argv.append ('-g')
        
            for in_file, out_file in zip(args.in_files, out_files):
                if _bc_or_ll_file (in_file): continue

                # clone argv
                argv1 = list ()
                argv1.extend (argv)

                if out_file is not None:
                    argv1.extend (['-o', out_file])

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
    
class LinkRt(sea.LimitedCmd):
    """
    Create an executable by linking with sea-rt library 
    """
    def __init__ (self, quiet=False):
        super (LinkRt, self).__init__('linkrt', 'Link sea-rt library', allow_extra=True)
        self.clangCmd = None

    def mk_arg_parser (self, ap):
        ap = super (LinkRt, self).mk_arg_parser (ap)
        ap.add_argument ('-m', type=int, dest='machine',
                         help='Machine architecture MACHINE:[32,64]', default=32)
        ap.add_argument ('-g', default=False, action='store_true',
                         dest='debug_info', help='Compile with debug info')
        add_in_out_args (ap)
        return ap

    def name_out_file (self, in_files, args=None, work_dir=None):
        assert (len (in_files) == 1)
        return _remap_file (in_files[0], '', work_dir)

    def run (self, args, extra):

        cmd_name = which (['clang++-mp-3.6', 'clang++-3.6', 'clang++',
                           'clang++-mp-3.5', 'clang++-mp-3.4'])
            
        if cmd_name is None: raise IOError ('clang++ not found')
        self.clangCmd = sea.ExtCmd (cmd_name)

        argv = []
        argv.append ('-m{0}'.format (args.machine))
        if args.debug_info: argv.append ('-g')

        if args.out_file is not None:
            argv.extend (['-o', args.out_file])

        assert (len (args.in_files) == 1)
        argv.append (args.in_files[0])
        
        lib_dir = os.path.dirname (sys.argv[0])
        lib_dir = os.path.dirname (lib_dir)
        lib_dir = os.path.join (lib_dir, 'lib')
        libseart = os.path.join (lib_dir, 'libsea-rt.a')
        argv.append (libseart)
        
        ret = self.clangCmd.run (args, argv)
        if ret <> 0: return ret

    @property
    def stdout (self):
        return self.clangCmd.stdout

## This function searches for `--dsa` option passed by `sea horn` command.
def get_sea_horn_dsa (opts):
    for x in opts:
        if x.startswith ('--dsa='):
            y = x[len('--dsa='):]
            if y == 'sea-flat' or y == 'sea-ci' or  y == 'sea-cs' or \
               y == 'llvm':
                return y
    return None
    
class Seapp(sea.LimitedCmd):
    def __init__(self, quiet=False, internalize=False, strip_extern=False):
        super(Seapp, self).__init__('pp', 'Pre-processing', allow_extra=True)
        self._internalize = internalize
        self._strip_extern = strip_extern
        
    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        assert (len(in_files) == 1)
        
        if self._strip_extern: ext = '.ext.bc'
        elif self._internalize: ext = '.int.bc'
        else: ext = '.pp.bc'
        
        # if args.llvm_asm: ext = '.pp.ll'
        return _remap_file_name (in_files[0], ext, work_dir)
        
    def mk_arg_parser (self, ap):
        ap = super (Seapp, self).mk_arg_parser (ap)
        ap.add_argument ('--inline', dest='inline', help='Inline all functions',
                         default=False, action='store_true')
        ap.add_argument ('--inline-only',
                         help='Inline only these functions',
                         dest='inline_only', type=str, metavar='str,...')
        ap.add_argument ('--inline-allocators', dest='inline_alloc', 
                         help='Inline functions that (de)allocate memory',
                         default=False, action='store_true')
        ap.add_argument ('--inline-constructors', dest='inline_const', 
                         help='Inline C++ constructors/destructors',
                         default=False, action='store_true')
        ap.add_argument ('--no-promote-assumptions', dest='no_promote_assumptions', 
                         help='Do not promote verifier.assume to llvm.assume',
                         default=False, action='store_true')        
        ap.add_argument ('--simplify-pointer-loops', dest='simp_ptr_loops', 
                         help='Simplify loops that iterate over pointers',
                         default=False, action='store_true')
        ap.add_argument ('--unfold-loops-for-dsa', dest='unfold_loops_for_dsa', 
                         help='Unfold the first loop iteration if useful for DSA analysis',
                         default=False, action='store_true')
        ap.add_argument ('--abstract-memory',
                         help='Abstract memory instructions', dest='abs_mem_lvl',
                         choices=['none','only-load','only-store','load-and-store'],
                         default='none')
        ap.add_argument ('--entry', dest='entry', help='Make entry point if main does not exist',
                         default=None, metavar='str')
        ap.add_argument ('--abc', dest='abc', 
                         help='Encoding used to insert array bounds checks',
                         choices=['none','local','global','global-c'], default='none')
        ap.add_argument ('--abc-disable-underflow', dest='abc_no_under',
                         help='Do not instrument for underflow checks',
                         default=False, action='store_true')
        ap.add_argument ('--abc-disable-reads', dest='abc_no_reads',
                         help='Do not instrument memory reads',
                         default=False, action='store_true')
        ap.add_argument ('--abc-disable-writes', dest='abc_no_writes',
                         help='Do not instrument memory writes',
                         default=False, action='store_true')
        ap.add_argument ('--abc-disable-mem-intrinsics', dest='abc_no_intrinsics',
                         help='Do not instrument memcpy, memmove, and memset',
                         default=False, action='store_true')
        ap.add_argument ('--abc-escape-ptr', dest='abc_escape_ptr',
                         help='Keep track whether a pointer escapes',
                         default=False, action='store_true')
        ap.add_argument ('--abc-use-deref', dest='abc_use_deref',
                         help='Use dereferenceable attribute to add extra assumptions',
                         default=False, action='store_true')
        ap.add_argument ('--abc-track-base-only', dest='abc_track_base_only',
                         help='Track only accesses to base pointers',
                         default=False, action='store_true')
        ap.add_argument ('--abc-surface-only', dest='abc_surface_only',
                         help='Track only accesses to pointers which are not stored in memory',
                         default=False, action='store_true')
        ap.add_argument ('--abc-store-base-only', dest='abc_store_base_only',
                         help='Check that only base pointers are stored in memory',
                         default=False, action='store_true')
        ap.add_argument ('--abc-dsa', 
                         help='Heap analysis used by abc instrumentation: '
                         'context-insensitive Llvm Dsa, '
                         'flat memory SeaHorn Dsa, '
                         'context-insensitive SeaHorn Dsa, and '
                         'context-sensitive SeaHorn Dsa',
                         choices=['llvm','sea-flat','sea-ci','sea-cs'],
                         dest='dsa', default='llvm')
        ap.add_argument ('--abc-dsa-node', dest='abc_dsa', 
                         help='Instrument only pointers that belong to this DSA node N',
                         type=int, default=0, metavar='N')
        ap.add_argument ('--abc-dsa-stats', dest='abc_dsa_stats',
                         help='Print some DSA stats before abc instrumentation',
                         default=False, action='store_true')
        ap.add_argument ('--abc-dsa-to-file', dest='abc_dsa_to_file',
                         help='Dump some Dsa info to a file',
                         metavar='DIR', default=None)        
        ap.add_argument ('--abc-alloc-site', dest='abc_site', 
                         help='Instrument only pointers  that belong to this allocation site N',
                         type=int, default=0, metavar='N')
        ap.add_argument ('--abc-instrument-only-types', 
                         help='Instrument only pointers of these user-defined types',
                         dest='abc_only_types', type=str,metavar='str,...')
        ap.add_argument ('--abc-instrument-except-types', 
                         help='Do not instrument a pointer if it is not of these user-defined types',
                         dest='abc_except_types', type=str,metavar='str,...')
        ap.add_argument ('--ndc', dest='ndc',
                         help='Insert null dereference checks',
                         default=False, action='store_true')
        ap.add_argument ('--ndc-opt', dest='ndc_opt',
                         help='Minimize the number of null dereference checks',
                         default=False, action='store_true')        
        ap.add_argument ('--externalize-addr-taken-functions',
                         help='Externalize uses of address-taken functions',
                         dest='enable_ext_funcs', default=False,
                         action='store_true')
        ap.add_argument ('--externalize-functions',
                         help='Externalize these functions',
                         dest='extern_funcs', type=str, metavar='str,...')
        ap.add_argument ('--enum-verifier-calls', dest='enum_verifier_calls',
                         help='Assign an unique identifier to each verifier.error call',
                         default=False, action='store_true')
        ap.add_argument ('--lower-invoke',
                         help='Lower invoke instructions',
                         dest='lower_invoke', default=False,
                         action='store_true')
        ap.add_argument ('--devirt-functions',
                         help='Devirtualize indirect functions',
                         dest='devirt_funcs', default=False,
                         action='store_true')
        ap.add_argument ('--lower-assert',
                         help='Replace assertions with assumptions',
                         dest='lower_assert', default=False,
                         action='store_true')
        ap.add_argument ('--no-kill-vaarg', help='Do not delete variadic functions',
                         dest='kill_vaarg', default=True, action='store_false')
        ap.add_argument ('--strip-extern', help='Replace external function calls ' + 
                         'by non-determinism', default=False, action='store_true',
                         dest='strip_external')
        ap.add_argument ('--slice-functions', 
                         help='Slice program onto these functions',
                         dest='slice_funcs', type=str, metavar='str,...')
        ap.add_argument ('--internalize', help='Create dummy definitions for all ' +
                         'external functions', default=self._internalize,
                         action='store_true', dest='internalize')
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
        if args.llvm_asm: argv.append ('-S')
        
        # internalize takes precedence over all other options and must run alone
        if self._strip_extern:
            argv.append ('--only-strip-extern=true')
        elif args.internalize:
            argv.append ('--klee-internalize')
        else:

            if args.inline: argv.append ('--horn-inline-all')
            else:
                if args.inline_only:
                    for f in args.inline_only.split(','):
                        argv.append ('--horn-inline-only={0}'.format(f))
                if args.inline_alloc: argv.append ('--horn-inline-allocators')
                if args.inline_const: argv.append ('--horn-inline-constructors') 
            
            if args.strip_external:
                argv.append ('--strip-extern=true')
            else:
                argv.append ('--strip-extern=false')
            
            if args.no_promote_assumptions:
                argv.append ('--promote-assumptions=false')
                
            if args.abs_mem_lvl <> 'none':
                argv.append ('--abstract-memory')
                argv.append ('--abstract-memory-level={0}'.format(args.abs_mem_lvl))
                
            if args.simp_ptr_loops:
                argv.append('--simplify-pointer-loops')

            if args.unfold_loops_for_dsa:
                argv.append('--unfold-loops-for-dsa')
            
            if args.lower_invoke:
                argv.append ('--lower-invoke')

            if args.devirt_funcs:
                argv.append ('--devirt-functions')
            
            if args.enable_ext_funcs:
                argv.append ('--externalize-addr-taken-funcs')

            if args.lower_assert: argv.append('--lower-assert')                           
                
            if args.abc <> 'none':
                argv.append ('--abc={0}'.format(args.abc))

                ## Begin Dsa options
                
                ## XXX: for simplicity, we enforce that --abc-dsa
                ## (from `sea pp`) and --dsa (from `sea horn`) options are the same.
                sea_horn_dsa = get_sea_horn_dsa (extra)
                if sea_horn_dsa is not None and sea_horn_dsa != args.dsa:
                    if args.dsa != 'llvm': ## do not bother warning if default value
                        print "WARNING: Overwriting \'--abc-dsa\' with \'--dsa\'."
                    args.dsa = sea_horn_dsa
                if args.dsa == 'llvm':
                    if args.abc_dsa_stats:
                        argv.append ('--llvm-dsa-stats') 
                    if args.abc_dsa_to_file is not None:
                        argv.append ('--dsa-info-to-file={n}'.format(n=args.abc_dsa_to_file))
                else:
                    if args.abc_dsa_stats:
                        argv.append ('--sea-dsa-stats')
                    if args.abc_dsa_to_file is not None:                        
                        argv.append ('--sea-dsa-info-to-file={n}'.format(n=args.abc_dsa_to_file))
                    ## we tell abc to use sea-dsa    
                    argv.append ('--abc-sea-dsa')
                    ## we select the sea-dsa variant
                    if args.dsa == 'sea-flat':
                        argv.append ('--sea-dsa=flat')
                    elif args.dsa == 'sea-ci':
                        argv.append ('--sea-dsa=ci')                        
                    else:
                        argv.append ('--sea-dsa=cs')
                ## End Dsa options

                argv.append ('--abc-dsa-node={n}'.format (n=args.abc_dsa))
                argv.append ('--abc-alloc-site={n}'.format (n=args.abc_site))
                if args.abc_only_types: 
                    for t in args.abc_only_types.split(','):
                        argv.append ('--abc-instrument-only-type={0}'.format(t))
                if args.abc_except_types: 
                    for t in args.abc_except_types.split(','):
                        argv.append ('--abc-instrument-except-type={0}'.format (t))
                if args.abc_no_under: argv.append ('--abc-instrument-underflow=false') 
                if args.abc_no_reads: argv.append ('--abc-instrument-reads=false') 
                if args.abc_no_writes: argv.append ('--abc-instrument-writes=false') 
                if args.abc_no_intrinsics: argv.append ('--abc-instrument-mem-intrinsics=false') 
                if args.abc_escape_ptr: argv.append ('--abc-escape-ptr') 
                if args.abc_use_deref: argv.append ('--abc-use-deref') 
                if args.abc_track_base_only: argv.append ('--abc-track-base-only')
                if args.abc_surface_only: argv.append ('--abc-surface-only')
                if args.abc_store_base_only: argv.append ('--abc-store-base-only')
                
            if args.extern_funcs:
                for f in args.extern_funcs.split(','):
                    argv.append ('--externalize-function={0}'.format(f))

            if args.slice_funcs:
                for f in args.slice_funcs.split(','):
                    argv.append ('--slice-function={0}'.format(f))
                
            if args.enum_verifier_calls:
                argv.append ('--enum-verifier-calls')

            if args.ndc:
                argv.append ('--null-check')
                if args.ndc_opt:
                    argv.append ('--null-check-optimize')
            
            if args.entry is not None:
                argv.append ('--entry-point={0}'.format (args.entry))

            if args.kill_vaarg:
                argv.append('--kill-vaarg=true')
            else:
                argv.append('--kill-vaarg=false')
                
        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])

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
        # some passes only after mixed semantics
        ap.add_argument ('--symbolize-constant-loop-bounds', dest='sym_bounds', 
                         help='Convert constant loop bounds into symbolic ones',
                         default=False, action='store_true')
        ap.add_argument ('--ms-slice-functions', 
                         help='Slice program onto these functions after mixed semantics',
                         dest='ms_slice_funcs', type=str)

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
        if args.sym_bounds:
            argv.append ('--horn-symbolize-loops')
            argv.append ('--promote-assumptions=false')            
        if args.ms_slice_funcs:
            for f in args.ms_slice_funcs.split(','):
                argv.append ('--slice-function={0}'.format(f))
            
        if args.llvm_asm: argv.append ('-S')
        argv.extend (args.in_files)
        return self.seappCmd.run (args, argv)
    
class WrapMem(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(WrapMem, self).__init__('wmem', 'Wrap external memory access with SeaRt calls',
                                       allow_extra=True)
        self.seppCmd = None

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        assert (len (in_files) == 1)
        
        ext = '.wmem.bc'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (WrapMem, self).mk_arg_parser (ap)
        ap.add_argument ('--no-wmem', dest='wmem_skip', help='Skipped wrap-mem pass',
                         default=False, action='store_true')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name)

        if args.wmem_skip:
            if args.out_file is not None:
                shutil.copy2 (args.in_files[0], args.out_file)
            return 0
        else:
            argv = list()
            if args.out_file is not None: argv.extend (['-o', args.out_file])
            argv.append ('--wrap-mem')
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
                         type=int, metavar='NUM',
                         help='Inline threshold (default = 255)')
        ap.add_argument ('--llvm-unroll-threshold', type=int,
                         help='Unrolling threshold (default = 150)',
                         dest='unroll_threshold',
                         default=150, metavar='NUM')
        ap.add_argument ('--enable-vectorize', dest='enable_vectorize', default=False,
                         action='store_true', help='Enable LLVM vectorization optimizations')
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
        if args.unroll_threshold is not None:
            argv.append ('--unroll-threshold={t}'.format
                         (t=args.unroll_threshold))
        if not args.enable_vectorize:
            argv.extend (['--disable-loop-vectorization=true',
                          '--disable-slp-vectorization=true',
                          '--vectorize-slp-aggressive=false'])

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
        ap.add_argument ('--threshold', type=int, help='Unrolling threshold. ' +
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

        # cannonical loops
        argv.append ('-loop-simplify')
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
        ap.add_argument ('--bv-cex', dest='bv_cex', help='Generate bit-precise counterexamples',
                         default=False, action='store_true')
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
                         choices=['small', 'large', 'fsmall', 'flarge', 'incsmall'],
                         dest='step', default='large')
        ap.add_argument ('--track',
                         help='Track registers, pointers, and memory',
                         choices=['reg', 'ptr', 'mem'], default='mem')
        ap.add_argument ('--dsa', 
                         help='Heap analysis used by \'mem\' encoding: '
                         'context-insensitive Llvm Dsa, '
                         'flat memory SeaHorn Dsa, '
                         'context-insensitive SeaHorn Dsa, and '
                         'context-sensitive SeaHorn Dsa',
                         choices=['llvm','sea-flat','sea-ci','sea-cs'],
                         dest='dsa', default='llvm')
        ap.add_argument ('--mem-dot',
                         help='Print Dsa memory graphs of all functions to dot format',
                         dest='mem_dot', default=False, action='store_true'),        
        ap.add_argument ('--show-invars',
                         help='Display computed invariants',
                         dest='show_invars', default=False, action='store_true')
        ap.add_argument ('--crab',
                         help='Enable Crab abstract interpreter',
                         dest='crab', default=False, action='store_true')
        ap.add_argument ('--bmc',
                         help='Use BMC engine',
                         dest='bmc', default=False, action='store_true')
        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seahornCmd = sea.ExtCmd (cmd_name)

        argv = list()

        if args.bmc:
            argv.append ('--horn-bmc')
            
        if args.crab:
            argv.append ('--horn-crab')

        if args.solve or args.out_file is not None:
            argv.append ('--keep-shadows=true')

            
        if args.dsa != 'llvm':
            if "--dsa-stats" in extra:
                argv.append ('--sea-dsa-stats')
            ## we tell abc to use sea-dsa    
            argv.append ('--horn-sea-dsa')
            ## we select the sea-dsa variant
            if args.dsa == 'sea-flat':
                argv.append ('--sea-dsa=flat')
            elif args.dsa == 'sea-ci':
                argv.append ('--sea-dsa=ci')                        
            else:
                argv.append ('--sea-dsa=cs')

        if args.mem_dot:
            if args.dsa == 'llvm':
                print ("WARNING: option --mem-dot only available if --dsa != llvm\n")
            else:
                argv.append ('--mem-dot')

        if args.solve:
            argv.append ('--horn-solve')
            # Cannot delete shadows since they are used by the solver
            if args.show_invars:
                argv.append ('--horn-answer')
        if args.cex is not None and args.solve:
            argv.append ('-horn-cex-pass')
            argv.append ('-horn-cex={0}'.format (args.cex))
            #argv.extend (['-log', 'cex'])
            if args.bv_cex:
                argv.append ('--horn-cex-bv=true')
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
        ap.add_argument ('--inv',
                         default=None, 
                         help='Save invariant into a file',
                         dest='inv')
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
        add_in_out_args (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seappCmd = sea.ExtCmd (cmd_name)

        argv = list()

        argv.append ('--horn-crab')
        argv.append ('--crab-add-invariants=all')

        if args.out_file is not None: argv.extend (['-oll', args.out_file])
        argv.extend (args.in_files)

        # pick out extra seahorn options
        argv.extend (filter (_is_seahorn_opt, extra))

        return self.seappCmd.run (args, argv)


class SeaTerm(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (SeaTerm, self).__init__ ('term', 'SeaHorn Termination analysis ',
                                        allow_extra=True)


    @property
    def stdout (self):
        return

    def name_out_file (self, in_files, args=None, work_dir=None):
        return _remap_file_name (in_files[0], '.smt2', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (SeaTerm, self).mk_arg_parser (ap)
        ap.add_argument ('--rank_func',
                         help='Choose Ranking Function Type',
                         choices=['max','lex','mul'], default='lex', dest='rank')
        return ap

    def run(self, args, extra):
        try:
            import term.termination as tt
            tt.seaTerm(extra[len(extra)-1],args.rank)
        except Exception as e:
            raise IOError(str(e))

## XXX: we prefer not to expose SeaInc to users.
#       That is, 'inc' is not an option of the 'sea' command.
class SeaInc(sea.LimitedCmd):
  def __init__ (self, quiet=False):
      super (SeaInc, self).__init__ ('inc',
                                     'Helper for inconsistency analysis',
                                      allow_extra=True)
  @property
  def stdout (self):
      return

  def name_out_file (self, in_files, args=None, work_dir=None):
      return _remap_file_name (in_files[0], '.smt2', work_dir)

  def mk_arg_parser (self, ap):
      ap = super (SeaInc, self).mk_arg_parser (ap)
      ap.add_argument ('--stop', help='stop after n iterations', dest="stop",
                       default=None, type=int)
      ap.add_argument ('--all', help='assert all failing flags', dest="all",
                      default=False,action='store_true')
      ap.add_argument ('--bench', help='Output Benchmarking Info', action='store_true',
                       default=False, dest="bench")
      ap.add_argument ('--debug_cex', help='Print RAW CEX for debugging', action='store_true',
                      default=False, dest="debug_cex")
      ap.add_argument ('--inv', help='Outpu Invariants', action='store_true',
                  default=False, dest="inv")
      ap.add_argument ('--stat', help='Print statistics', dest="stat",
                  default=False, action='store_true')
      ap.add_argument ('--spacer_verbose', help='Spacer Verbose', action='store_true',
                       default=False, dest="z3_verbose")
      ap.add_argument ('--no_dl', help='Disable Difference Logic (UTVPI) in SPACER',
                       action='store_true',
                       default=False, dest="utvpi")
      ap.add_argument ('--pp',
                       help='Enable default pre-processing in the solver',
                       action='store_true', default=False)
      ap.add_argument ('--inc_verbose', help='Verbose', action='store_true',
                       default=False, dest="inc_verbose")
      ap.add_argument ('--save', help='Save results file', action='store_true',
                      default=False, dest="save")
      ap.add_argument ('--timeout', help='Timeout per function',
                      type=float, default=20.00, dest="timeout")
      ap.add_argument ('--func', help='Number of functions',
                      type=int, default=-1, dest="func")
      return ap

  def run(self, args, extra):
      try:
          # from inc.inc import Inc
          # tt = Inc(args)
          # tt.solve(extra[len(extra)-1])
          from inc.par_inc import JobsSpanner
          jb = JobsSpanner(args)
          smt2_file = extra[len(extra)-1]
          jb.singleRun(smt2_file)
      except Exception as e:
          raise IOError(str(e))

class SeaAbc(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (SeaAbc, self).__init__ ('abc', allow_extra=True)
        self.help = 'SeaHorn array bounds check analysis '

    @property
    def stdout (self):
        return

    def name_out_file (self, in_files, args=None, work_dir=None):
        return _remap_file_name (in_files[0], '.smt2', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (SeaAbc, self).mk_arg_parser (ap)
        add_in_out_args(ap)
        add_tmp_dir_args(ap)
        import sea.abc as abc
        abc.add_abc_args(ap)
        return ap

    def run(self, args, extra):
        try:
            import sea.abc as abc
            return abc.sea_abc(args, extra)
        except Exception as e:
            raise IOError(str(e))


class SeaInspect(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (SeaInspect, self).__init__ ('inspect', allow_extra=True)
        self.help = 'Utilities for program inspection'

    @property
    def stdout (self):
        return self.seainspectCmd.stdout

    def mk_arg_parser (self, ap):
        ap = super (SeaInspect, self).mk_arg_parser (ap)
        add_in_out_args (ap)
        ap.add_argument ('--profiler', default=False, action='store_true',
                         dest='profiling', help='Profile program for static analysis')
        ap.add_argument ('--cfg-dot', default=False, action='store_true',
                         dest='cfg_dot', help='Print CFG of all functions to dot format')
        ap.add_argument ('--cfg-only-dot', default=False, action='store_true',
                         dest='cfg_only_dot', help='Print CFG of all functions (without instructions) to dot format')
        ap.add_argument ('--mem-dot', default=False, action='store_true',
                         dest='mem_dot', help='Print memory graph of all functions to dot format')
        ap.add_argument ('--dot-outdir', default="", type=str, metavar='DIR', 
                         dest='dot_outdir', help='Directory to store all dot files')
        ap.add_argument ('--cfg-viewer', default=False, action='store_true',
                         dest='cfg_viewer', help='View CFG of all functions to dot format')
        ap.add_argument ('--cfg-only-viewer', default=False, action='store_true',
                         dest='cfg_only_viewer', help='View CFG of all functions (without instructions) to dot format')
        ap.add_argument ('--mem-viewer', default=False, action='store_true',
                         dest='mem_viewer', help='View memory graph of all functions to dot format')
        ap.add_argument ('--mem-stats', default=False, action='store_true',
                         dest='mem_stats', help='Print stats about all memory graphs')
        return ap

    def run (self, args, extra):
        cmd_name = which ('seainspect')
        if cmd_name is None: raise IOError ('seainspect not found')
        self.seainspectCmd = sea.ExtCmd (cmd_name)

        argv = list()

        if args.profiling: argv.extend (['-profiler'])
        if args.cfg_dot: argv.extend (['-cfg-dot'])
        if args.cfg_only_dot: argv.extend (['-cfg-only-dot'])
        if args.cfg_viewer: argv.extend (['-cfg-viewer'])
        if args.cfg_only_viewer: argv.extend (['-cfg-only-viewer'])
        if args.mem_dot: argv.extend (['-mem-dot'])
        if args.mem_viewer: argv.extend (['-mem-viewer'])
        if args.mem_stats: argv.extend (['-mem-stats'])                                
        if args.mem_dot or args.mem_viewer:
            if args.dot_outdir is not "":
                argv.extend(['-sea-dsa-dot-outdir={0}'.format(args.dot_outdir)])

        dsa = get_sea_horn_dsa (extra)
        if dsa is not None:
            ## we select the sea-dsa variant
            if dsa == 'sea-flat':
                argv.extend (['--sea-dsa=flat'])
            elif dsa == 'sea-ci':
                argv.extend (['--sea-dsa=ci'])
            else:
                argv.extend (['--sea-dsa=cs'])
            
        argv.extend (args.in_files)
        # pick out extra seahorn options
        argv.extend (filter (_is_seahorn_opt, extra))

        return self.seainspectCmd.run (args, argv)

## SeaHorn commands

## SeaHorn commands
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
seaTerm = sea.SeqCmd ('term', 'SeaHorn Termination analysis', Smt.cmds + [SeaTerm()])
ClangPP = sea.SeqCmd ('clang-pp', 'alias for clang|pp', [Clang(), Seapp()])
seaIncSmt = sea.SeqCmd ('inc-smt', 'alias for fe|horn|inc. ' +
                        'It should be used only as a helper by sea_inc.',
                        Smt.cmds + [SeaInc()])
seaClangAbc = sea.SeqCmd ('clang-abc', 'alias for clang|abc', [Clang(), SeaAbc()])
Exe = sea.SeqCmd ('exe', 'alias for clang|pp --strip-extern|pp --internalize|wmem|linkrt',
                  [Clang(), Seapp(strip_extern=True), Seapp(internalize=True), WrapMem(), LinkRt()])
feInspect = sea.SeqCmd ('fe-inspect', 'alias for fe + seainspect', FrontEnd.cmds + [SeaInspect()])
                         
