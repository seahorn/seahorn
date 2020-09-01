import sea

import os.path
import sys
import shutil

import subprocess

from sea import add_in_args, add_in_out_args, add_tmp_dir_args, add_bool_argument, which, createWorkDir

# To disable printing of commands and some warnings
quiet=False

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

def _plus_plus_file (name):
    ext = os.path.splitext (name)[1]
    return ext == '.cpp' or ext == '.cc'

class Clang(sea.LimitedCmd):
    """
    Produce bitcode for each C/C++ file and link together the generated
    bitcode files. If the input files are already bitcode then we
    still link them together.
    """

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
            if _plus_plus_file (in_file):
                self.plusplus = True
        else:
            in_file = 'merged.c'
            if all ((_plus_plus_file(f) or _bc_or_ll_file(f)) for f in in_files):
                self.plusplus = True
        ext = '.bc'
        # if args.llvm_asm: ext = '.ll'
        return _remap_file_name (in_file, ext, work_dir)

    def run (self, args, extra):

        def link_bc_files(bc_files, args):
            if len(bc_files) <= 1:
                return 0
            cmd_name = which (['llvm-link-mp-10', 'llvm-link-10', 'llvm-link'])
            if cmd_name is None: raise IOError ('llvm-link not found')
            self.linkCmd = sea.ExtCmd (cmd_name,'',quiet)

            argv = []
            if args.llvm_asm: argv.append ('-S')
            if args.out_file is not None:
                argv.extend (['-o', args.out_file])
            argv.extend (bc_files)
            return self.linkCmd.run (args, argv)

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

        # do nothing on .bc and .ll files except link them together
        if _bc_or_ll_file (args.in_files[0]):
            return link_bc_files(out_files, args)

        if self.plusplus:
            cmd_name = which (['clang++-mp-10', 'clang++-10', 'clang++'])
        else:
            cmd_name = which (['clang-mp-10', 'clang-10', 'clang'])

        if cmd_name is None: raise IOError ('clang not found')
        self.clangCmd = sea.ExtCmd (cmd_name,'',quiet)

        if not all (_bc_or_ll_file (f) for f  in args.in_files):
            argv = ['-c', '-emit-llvm', '-D__SEAHORN__']

            # in clang-5.0 to ensure that compilation is done without
            # optimizations and also does not mark produced bitcode
            # to not be optimized or not be inlined, compile
            # with optimizations (-O1) and ask clang to not apply them
            argv.extend (['-O1', '-Xclang', '-disable-llvm-optzns'])

            if not self.plusplus:
                ## this is an invalid argument with C++/ObjC++ with clang 3.8
                argv.append('-fgnu89-inline')
            else:
                ## flags to tell clang to build C++ type information for vtables.
                argv.append('-flto')
                argv.append('-fvisibility=hidden')
                argv.append('-fwhole-program-vtables')

            argv.extend ([s for s in extra if s.startswith ('-D')])

            if args.llvm_asm: argv.append ('-S')
            argv.append ('-m{0}'.format (args.machine))

            if args.include_dir is not None:
                if ':' in args.include_dir:
                    idirs = ["-I{}".format(x.strip())  \
                      for x in args.include_dir.split(":") if x.strip() != '']
                    argv.extend(idirs)
                else:
                    argv.append ('-I' + args.include_dir)

            include_dir = os.path.dirname (sys.argv[0])
            include_dir = os.path.dirname (include_dir)
            include_dir = os.path.join (include_dir, 'include')
            argv.append ('-I' + include_dir)

            if args.debug_info: argv.append ('-g')

            ## Hack for OSX Mojave that no longer exposes libc and libstd headers by default
            osx_sdk_dirs = ['/Applications/Xcode.app/Contents/Developer/Platforms/' + \
                            'MacOSX.platform/Developer/SDKs/MacOSX10.14.sdk',
                            '/Applications/Xcode.app/Contents/Developer/Platforms/' + \
                            'MacOSX.platform/Developer/SDKs/MacOSX10.15.sdk']

            for osx_sdk_dir in osx_sdk_dirs:
                if os.path.isdir(osx_sdk_dir):
                    argv.append('--sysroot=' + osx_sdk_dir)
                    break

            for in_file, out_file in zip(args.in_files, out_files):
                if _bc_or_ll_file (in_file): continue

                # clone argv
                argv1 = list ()
                argv1.extend (argv)

                if out_file is not None:
                    argv1.extend (['-o', out_file])

                argv1.append (in_file)
                ret = self.clangCmd.run (args, argv1)
                if ret != 0: return ret

        return link_bc_files(out_files, args)

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
        ap.add_argument ('-alloc-mem', '--alloc-mem', default=False, action='store_true',
                         dest='alloc_mem',
                         help='Allocate memory for uninitialized memory')
        add_in_out_args (ap)
        return ap

    def name_out_file (self, in_files, args=None, work_dir=None):
        assert (len (in_files) == 1)
        return _remap_file (in_files[0], '', work_dir)

    def run (self, args, extra):

        cmd_name = which (['clang++-mp-10', 'clang++-10', 'clang++'])

        if cmd_name is None: raise IOError ('clang++ not found')
        self.clangCmd = sea.ExtCmd (cmd_name,'',quiet)

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
        if args.alloc_mem:
            libseart = os.path.join (lib_dir, 'libsea-mem-rt.a')
        else:
            libseart32 = os.path.join(lib_dir, 'libsea-rt-32.a')
            if args.machine == 32 and os.path.exists(libseart32):
                libseart = libseart32
            else:
                libseart = os.path.join (lib_dir, 'libsea-rt.a')
        argv.append (libseart)

        return self.clangCmd.run (args, argv)

    @property
    def stdout (self):
        return self.clangCmd.stdout

## This function searches for `--dsa` option passed by `sea horn` command.
def get_sea_horn_dsa (opts):
    for x in opts:
        if x.startswith ('--dsa='):
            y = x[len('--dsa='):]
            if y == 'sea-flat' or y == 'sea-ci' or  y == 'sea-cs':
                return y
    return None

class Seapp(sea.LimitedCmd):
    def __init__(self, quiet=False, internalize=False, strip_extern=False,
                 keep_lib_fn=False):
        super(Seapp, self).__init__('pp', 'Pre-processing', allow_extra=True)
        self._internalize = internalize
        self._strip_extern = strip_extern
        self._keep_lib_fn = keep_lib_fn

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

    import argparse
    class DevirtAction(argparse.Action):
        def __call__(self, parser, namespace, values, option_string=None):
            if values is None:
                setattr(namespace, self.dest, 'types')
            else:
                setattr(namespace, self.dest, values)

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
        ap.add_argument ('--promote-assumptions', dest='promote_assumptions',
                         help='Promote verifier.assume to llvm.assume',
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
        ap.add_argument('--no-lower-gv-init-structs',
                        dest='no_lower_gv_init_structs',
                        help='Do not lower global initializers for structs',
                        default=False,
                        action='store_true')
        ap.add_argument('--no-lower-gv-init',
                        dest='no_lower_gv_init',
                        help='Do not lower global initializers',
                        default=False,
                        action='store_true')
        ap.add_argument('--devirt-functions',
                        help="Devirtualize indirect calls (needed for soundness):\n"
                        "- none : do not resolve indirect calls (default)\n"
                        "- types: select all functions with same type signature\n"
                        "- sea-dsa: use sea-dsa+types analysis to select the callees\n",
                        nargs='?',
                        default='none',
                        dest='devirt_funcs',
                        metavar='none|types|sea-dsa',
                        action=self.DevirtAction)
        ap.add_argument ('--devirt-functions-with-cha',
                         help="Devirtualize indirect functions using CHA (for C++). "
                         "This method only inspects the virtual tables to devirtualize. "
                         "Use --devirt-function to devirtualize other calls",
                         dest='devirt_funcs_cha', default=False,
                         action='store_true')
        ap.add_argument ('--devirt-functions-allow-indirect-calls',
                         help="Keep original indirect call if all callees might not be known",
                         dest='devirt_allow_indirect', default=False,
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
        ap.add_argument ('--sea-dsa-log', dest='dsa_log', default=None,
                         metavar='STR', help='Log level for sea-dsa')

        add_bool_argument(ap, 'with-arith-overflow', dest='with_arith_overflow',
                          help='Allow arithmetic overflow intrinsics')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()

        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if args.llvm_asm: argv.append ('-S')

        # disable sinking instructions to end of basic block
        # this might create unwanted aliasing scenarios
        # for now, there is no option to undo this switch
        argv.append('--simplifycfg-sink-common=false')

        # internalize takes precedence over all other options and must run alone
        if self._strip_extern:
            argv.append ('--only-strip-extern=true')
            if self._keep_lib_fn:
                argv.append ("--keep-lib-fn")
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

            if args.promote_assumptions:
                argv.append ('--promote-assumptions=true')
            else:
                argv.append ('--promote-assumptions=false')


            if args.abs_mem_lvl != 'none':
                argv.append ('--abstract-memory')
                argv.append ('--abstract-memory-level={0}'.format(args.abs_mem_lvl))

            if args.simp_ptr_loops:
                argv.append('--simplify-pointer-loops')

            if args.unfold_loops_for_dsa:
                argv.append('--unfold-loops-for-dsa')

            if args.lower_invoke:
                argv.append ('--lower-invoke')

            if args.no_lower_gv_init_structs:
                argv.append('--lower-gv-init-struct=false')

            if args.no_lower_gv_init:
                argv.append('--lower-gv-init=false')

            if args.devirt_funcs_cha or args.devirt_funcs != 'none':
                argv.append ('--devirt-functions')
                if args.devirt_allow_indirect:
                    argv.append('--devirt-functions-allow-indirect-calls')
            if args.devirt_funcs != 'none':
                argv.append ('--devirt-functions-method={0}'.format(args.devirt_funcs))
            if args.devirt_funcs_cha:
                argv.append ('--devirt-functions-with-cha')

            if args.enable_ext_funcs:
                argv.append ('--externalize-addr-taken-funcs')

            if args.lower_assert: argv.append('--lower-assert')

            if args.extern_funcs:
                for f in args.extern_funcs.split(','):
                    argv.append ('--externalize-function={0}'.format(f))

            if args.slice_funcs:
                for f in args.slice_funcs.split(','):
                    argv.append ('--slice-function={0}'.format(f))

            if args.enum_verifier_calls:
                argv.append ('--enum-verifier-calls')

            if args.entry is not None:
                argv.append ('--entry-point={0}'.format (args.entry))

            if args.kill_vaarg:
                argv.append('--kill-vaarg=true')
            else:
                argv.append('--kill-vaarg=false')

            if args.with_arith_overflow:
                argv.append('--horn-keep-arith-overflow=true')
            else:
                argv.append('--horn-keep-arith-overflow=false')


        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        if args.dsa_log is not None:
            for l in args.dsa_log.split (':'): argv.extend (['-log', l])

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
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()

        # disable sinking instructions to end of basic block
        # this might create unwanted aliasing scenarios
        # for now, there is no option to undo this switch
        argv.append('--simplifycfg-sink-common=false')

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

class NdcInst(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(NdcInst, self).__init__('ndc-inst',
                                     'Null dereference Checks Instrumentation',
                                     allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        ext = '.abc.bc'
        # if args.llvm_asm: ext = '.ms.ll'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (NdcInst, self).mk_arg_parser (ap)
        ap.add_argument ('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        ap.add_argument ('--sea-dsa-log', dest='dsa_log', default=None,
                         metavar='STR', help='Log level for sea-dsa')
        ap.add_argument ('--ndc-opt', dest='ndc_opt',
                         help='Minimize the number of null dereference checks',
                         default=False, action='store_true')

        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if args.llvm_asm: argv.append ('-S')

        argv.append ('--null-check')
        if args.ndc_opt: argv.append ('--null-check-optimize')

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        if args.dsa_log is not None:
            for l in args.dsa_log.split (':'): argv.extend (['-log', l])

        argv.extend (args.in_files)
        return self.seappCmd.run(args, argv)

class SimpleMemoryChecks(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(SimpleMemoryChecks, self).__init__('smc',
                                                 'Simple Memory Safety Checks',
                                       allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        ext = '.smc.bc'
        # if args.llvm_asm: ext = '.ms.ll'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (SimpleMemoryChecks, self).mk_arg_parser (ap)
        ap.add_argument ('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        ap.add_argument ('--sea-dsa-log', dest='dsa_log', default=None,
                         metavar='STR', help='Log level for sea-dsa')
        ap.add_argument ('--print-smc-stats', default=False, action='store_true',
                         dest='print_smc_stats', help='Print Simple Memory Check stats')
        ap.add_argument ('--smc-check-threshold', type=int, dest='smc_check_threshold',
                         help='Max no. of analyzed memory instructions', default=100)
        ap.add_argument ('--smc-instrument-check', type=int, dest='smc_instrument_check',
                         help='Check id to instrement', default=0)
        ap.add_argument ('--smc-instrument-alloc', type=int, dest='smc_instrument_alloc',
                         help='Allocation site id to instrument', default=0)
        ap.add_argument ('--sea-dsa-type-aware', default=False, action='store_true',
                         dest='smc_type_aware', help='Use type-aware SeaDsa')

        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])
        if args.llvm_asm: argv.append ('-S')

        argv.append('--smc')
        argv.append('--sea-dsa-type-aware={t}'.format(t=args.smc_type_aware))

        if args.print_smc_stats:
            argv.append('--print-smc-stats')

        if args.smc_check_threshold is not None:
            argv.append ('--smc-check-threshold={t}'.format(t=args.smc_check_threshold))

        if args.smc_instrument_check is not None:
            argv.append ('--smc-instrument-check={t}'.format(t=args.smc_instrument_check))

        if args.smc_instrument_alloc is not None:
            argv.append ('--smc-instrument-alloc={t}'.format(t=args.smc_instrument_alloc))

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        if args.dsa_log is not None:
            for l in args.dsa_log.split (':'): argv.extend (['-log', l])

        argv.extend (args.in_files)
        return self.seappCmd.run(args, argv)


class RemoveTargetFeatures(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(RemoveTargetFeatures, self).__init__('rmtf', 'Remove redundant target-features from attributes',
                                                   allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        assert (len (in_files) == 1)

        ext = '.rmtf.bc'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super(RemoveTargetFeatures, self).mk_arg_parser (ap)
        add_bool_argument(ap, 'rmtf', dest='rm_tar_feat', help='Remove target-features from attributes')
        add_in_out_args(ap)
        return ap

    def run(self, args, _):
        import re
        if args.rm_tar_feat:
            if args.out_file is not None:
                fout = open(args.out_file, 'wt')
                fin = open(args.in_files[0], 'rt')

                for ln in fin:
                   fout.write(re.sub(r'"target-features"="[^"]+"', '', ln))

                fin.close()
                fout.close()
            return 0
        else:
            if args.out_file is not None:
                shutil.copy2 (args.in_files[0], args.out_file)
            return 0


class WrapMem(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(WrapMem, self).__init__('wmem', 'Wrap external memory access with SeaRt calls',
                                       allow_extra=True)
        self.seappCmd = None

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
        # add_bool_argument(ap, 'skip-wmem', dest='wmem_skip', help='Skipped wrap-mem pass')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

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

class ExecHarness(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(ExecHarness, self).__init__('exec-harness', 'Execute an executable harness to see if it calls __VERIFIER_error',
                                             allow_extra=True)
        self.harnessCmd = None

    @property
    def stdout (self):
        return self.harnessCmd.stdout

    def mk_arg_parser (self, ap):
        ap = super (ExecHarness, self).mk_arg_parser (ap)
        add_in_args (ap)
        return ap

    def run (self, args, extra):
        if len(args.in_files) != 1: raise IOError('ExecHarness expects the harness executable as an input')
        eharness = os.path.abspath(args.in_files[0])

        self.harnessCmd = sea.ExtCmd (eharness)
        if args.cpu is None: args.cpu = 10

        retval = self.harnessCmd.run (args, [eharness], encoding='utf-8', errors='replace', stdout=subprocess.PIPE)

        if "[sea] __VERIFIER_error was executed" in self.harnessCmd.stdout:
            print ("__VERIFIER_error was executed")
        else:
            print ("__VERIFIER_error was not executed")

        return retval

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
        ap.add_argument('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        ap.add_argument('--peel', dest='peel', default=0, metavar='NUM',
                        type=int, help='Number of iterations to peel loops')
        add_bool_argument(ap, 'assert-on-backedge', dest='assert_backedge',
                          default=False,
                          help='Add verifier.assert to check completeness of loop unrolling')

        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])

        if args.peel > 0:
            argv.append('-horn-peel-loops=' + str(args.peel))

        argv.append ('--horn-cut-loops')
        if args.llvm_asm: argv.append ('-S')

        if args.assert_backedge:
            argv.append('--back-edge-cutter-with-asserts=true')
        else:
            argv.append('--back-edge-cutter-with-asserts=false')


        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])

        argv.extend (args.in_files)
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
        cmd_name = which (['seaopt'])
        if cmd_name is None: raise IOError ('`seaopt` from llvm-seahorn (https://github.com/seahorn/llvm-seahorn) is not found')
        self.seaoptCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = ['-f']

        # disable sinking instructions to end of basic block
        # this might create unwanted aliasing scenarios
        # for now, there is no option to undo this switch
        argv.append('--simplifycfg-sink-common=false')


        if args.out_file is not None:
            argv.extend (['-o', args.out_file])
        if args.opt_level > 0 and args.opt_level <= 3:
            argv.append('-O{0}'.format (args.opt_level))

        if not args.enable_indvar:
            argv.append ('--seaopt-enable-indvar=false')
        if not args.enable_loop_idiom:
            argv.append ('--seaopt-enable-loop-idiom=false')
        # if not args.enable_nondet_init:
        #     argv.append ('--enable-nondet-init=false')
        if args.inline_threshold is not None:
            argv.append ('--inline-threshold={t}'.format(t=args.inline_threshold))
        if args.unroll_threshold is not None:
            argv.append ('--unroll-threshold={t}'.format
                         (t=args.unroll_threshold))

        # do not allow partial unrolling that introduces complex runtime code
        argv.extend(['--unroll-allow-partial=false',
                     '--unroll-partial-threshold=0'])

        if not args.enable_vectorize:
            argv.extend ([  '--vectorize-loops=false'
                          , '--disable-slp-vectorization=true'
                         ])

        argv.extend (args.in_files)
        if args.llvm_asm: argv.append ('-S')
        return self.seaoptCmd.run (args, argv)


class FatBoundsCheck(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(FatBoundsCheck, self).__init__('fat-bnd-check', 'Add fat bounds check instrumentation',
                                       allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        ext = '.fat.bc'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (FatBoundsCheck, self).mk_arg_parser (ap)
        ap.add_argument('--log', dest='log', default=None,
                        metavar='STR', help='Log level')
        ap.add_argument('--no-fat-fns', dest='no_fat_fns', default=None,
                        type=str, metavar='STR,STR,...', help='List of functions to NOT instrument')
        add_in_out_args (ap)
        _add_S_arg (ap)
        return ap

    def run (self, args, extra):
        cmd_name = which ('seapp')
        if cmd_name is None: raise IOError ('seapp not found')
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()
        if args.out_file is not None: argv.extend (['-o', args.out_file])

        argv.append ('-fat-bnd-check')

        if args.no_fat_fns is not None:
            argv.append('--no-bound-check-fns={fns}'.format(fns=args.no_fat_fns));

        # slots=false ==> use is_dereferenceable(...) instrumentation
        argv.append('--horn-bnd-chk-slots=false')
        if args.llvm_asm: argv.append ('-S')
        argv.extend (args.in_files)

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])

        return self.seappCmd.run (args, argv)


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
        cmd_name = which (['seaopt'])
        if cmd_name is None: raise IOError ('`seaopt` from llvm-seahorn (https://github.com/seahorn/llvm-seahorn) is not found')
        self.seaoptCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = ['-f']
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
    prefixes = ['horn-', 'crab', 'sea-opsem']
    if x.startswith ('-'):
        y = x.strip ('-')
        return any((y.startswith(p) for p in prefixes))
    return False

class Seahorn(sea.LimitedCmd):
    def __init__ (self, solve=False, enable_boogie = False, quiet=False):
        super (Seahorn, self).__init__ ('horn', 'Generate (and solve) ' +
                                        'Constrained Horn Clauses in SMT-LIB format',
                                        allow_extra=True)
        self.solve = solve
        self.enable_boogie = enable_boogie

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
        ap.add_argument ('--bv-chc', dest='bv_chc', help='Bit-precise CHC encoding',
                         default=False, action='store_true')
        ap.add_argument ('--solve', dest='solve', action='store_true',
                         help='Solve', default=self.solve)
        ap.add_argument ('--ztrace', dest='ztrace', metavar='STR',
                         default=None, help='Z3 trace levels')
        ap.add_argument ('--verbose', '-v', dest='verbose', type=int, default=0,
                         help='Verbosity level', metavar='N')
        ap.add_argument ('--log', dest='log', default=None,
                         metavar='STR', help='Log level')
        ap.add_argument ('--sea-dsa-log', dest='dsa_log', default=None,
                         metavar='STR', help='Log level for sea-dsa')
        ap.add_argument ('--crab-log', dest='crab_log', default=None,
                         metavar='STR', help='Log level for crab')
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
                         'sea-flat (flat memory SeaHorn Dsa), '
                         'sea-ci (context-insensitive SeaHorn Dsa), and '
                         'sea-cs (context-sensitive SeaHorn Dsa)',
                         choices=['sea-flat','sea-ci','sea-cs', 'sea-ci-t', 'sea-cs-t'],
                         dest='dsa', default='sea-ci')
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
                         choices=['none', 'mono', 'path', 'opsem'],
                         dest='bmc', default='none')
        ap.add_argument ('--max-depth',
                         help='Maximum depth of exploration',
                         dest='max_depth', default=sys.maxsize)
        ap.add_argument('--no-lower-gv-init',
                        dest='no_lower_gv_init',
                        help='Do not lower global initializers',
                        default=False,
                        action='store_true')
        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seahornCmd = sea.ExtCmd (cmd_name,'',quiet)
        argv = list()

        if args.max_depth != sys.maxsize:
            argv.append ('--horn-max-depth=' + str(args.max_depth))

        if args.bmc != 'none':
            argv.append ('--horn-bmc')
            if args.bmc == 'path':
                argv.append ('--horn-bmc-engine=path')
            elif args.bmc.startswith('opsem'):
                argv.append('--horn-bv2')
                argv.append('-log=opsem')
                argv.append('--lower-gv-init-struct=false')

        if args.crab:
            argv.append ('--horn-crab')

        if self.enable_boogie:
            argv.append ('--boogie')
            # the translation uses crab to add invariants: disable crab warnings
            # argv.append ('--crab-enable-warnings=false')

        if args.solve or args.out_file is not None:
            argv.append ('--keep-shadows=true')

        if "--dsa-stats" in extra:
            argv.append ('--sea-dsa-stats')

        ## sea-dsa: select variant
        if args.dsa == 'sea-flat':
            argv.append ('--sea-dsa=flat')
        elif args.dsa == 'sea-ci' or args.dsa == 'sea-ci-t':
            argv.append ('--sea-dsa=ci')
        else:
            argv.append ('--sea-dsa=cs')

        ## sea-dsa: enable type-awareness
        if args.dsa == 'sea-cs-t' or args.dsa == 'sea-ci-t':
           argv.append('--sea-dsa-type-aware')

        if args.mem_dot:
            argv.append ('--mem-dot')

        if args.bv_chc:
            argv.append('--horn-chc-bv')
            # bit-precise CHC implies bit-precise cex
            args.bv_cex = True

        if args.solve:
            argv.append ('--horn-solve')
            # Cannot delete shadows since they are used by the solver
            if args.show_invars:
                argv.append ('--horn-answer')
        if args.cex is not None and args.solve:
            argv.append ('-horn-cex-pass')
            argv.append ('-horn-cex={0}'.format (args.cex))
            if args.bv_cex:
                argv.append ('--horn-cex-bv=true')
        if args.asm_out_file is not None: argv.extend (['-oll', args.asm_out_file])

        argv.extend (['-horn-inter-proc',
                      '-horn-sem-lvl={0}'.format (args.track),
                      '--horn-step={0}'.format (args.step)])

        if args.verbose > 0:
            argv.extend (['-zverbose', str(args.verbose)])
            argv.extend (['-cverbose', str(args.verbose)])

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        if args.dsa_log is not None:
            for l in args.dsa_log.split (':'): argv.extend (['-log', l])
        if args.crab_log is not None:
            for l in args.crab_log.split (':'): argv.extend (['-crab-log', l])

        if args.ztrace is not None:
            for l in args.ztrace.split (':'): argv.extend (['-ztrace', l])

        if args.out_file is not None: argv.extend (['-o', args.out_file])

        if args.no_lower_gv_init:
            argv.append('--lower-gv-init=false')

        argv.extend (args.in_files)

        # pick out extra seahorn options
        sea_argv = list(filter (_is_seahorn_opt, extra))

        ###
        ### Unfortunately this prints the warning too often
        ### `extra` contains all options passed to the aggregate command
        ### on command line, so it is likely to contain non-seahorn options
        ### I thought that each sub-command 'eats' options it has processed,
        ### but this is not the case. Disabling to avoid even more confusion.
        ###
        # if len(sea_argv) <> len(extra):
        #     print ('WARNING: Ignoring unknown options:',
        #            ' '.join(filter(lambda x : not _is_seahorn_opt(x), extra)))

        argv.extend (sea_argv)


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
        ap.add_argument ('--sea-dsa-log', dest='dsa_log', default=None,
                         metavar='STR', help='Log level for sea-dsa')
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
        self.seahornCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()
        if args.asm_out_file is not None: argv.extend (['-oll', args.asm_out_file])

        argv.extend (['-horn-inter-proc',
                      '-horn-format=clp', '-horn-sem-lvl=reg',
                      '--horn-step={0}'.format (args.step)])

        if args.clp_fapp:
            argv.extend (['--horn-clp-fapp'])

        if args.log is not None:
            for l in args.log.split (':'): argv.extend (['-log', l])
        if args.dsa_log is not None:
            for l in args.dsa_log.split (':'): argv.extend (['-log', l])

        if args.out_file is not None: argv.extend (['-o', args.out_file])
        argv.extend (args.in_files)

        # pick out extra seahorn/crab options
        argv.extend (list(filter (_is_seahorn_opt, extra)))

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
            print ('LEGACY FRONT-END HAS BEEN DEPRECATED')
            print ('THE FOLLOWING INSTRUCTIONS ARE PROBABLY INCORRECT')
            print ('No legacy front-end found at:', cmd_name)
            print ('Download from https://bitbucket.org/arieg/seahorn-gh/downloads/seahorn-svcomp15-r1.tar.bz2 (64bit) or https://bitbucket.org/arieg/seahorn-gh/downloads/lfe32-2015.tar.bz2 (32bit) and extract into `legacy` sub-directory')
            print ('Only supported on Linux')
            return 1

        import subprocess
        self.lfeCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = ['--no-seahorn', '-o', args.out_file]
        argv.append ('-m{0}'.format (args.machine))
        if args.debug_info: argv.append ('--mark-lines')
        argv.extend (args.in_files)

        return self.lfeCmd.run (args, argv)

class CrabInst (sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (CrabInst, self).__init__ ('crab-inst',
                                         'Instrument LLVM bitcode with invariants inferred by Crab',
                                         allow_extra=True)

    @property
    def stdout (self):
        return self.seappCmd.stdout

    def name_out_file (self, in_files, args=None, work_dir=None):
        ext = 'crab.ll'
        return _remap_file_name (in_files[0], ext, work_dir)

    def mk_arg_parser (self, ap):
        ap = super (CrabInst, self).mk_arg_parser (ap)
        add_in_out_args (ap)
        ap.add_argument ('--crab-log', dest='crab_log', default=None,
                         metavar='STR', help='Log level for crab')
        return ap

    def run (self, args, extra):
        cmd_name = which ('seahorn')
        if cmd_name is None: raise IOError ('seahorn not found')
        self.seappCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()

        argv.append ('--horn-crab')
        argv.append ('--crab-add-invariants=all')

        if args.out_file is not None: argv.extend (['-oll', args.out_file])
        argv.extend (args.in_files)

        if args.crab_log is not None:
            for l in args.crab_log.split (':'): argv.extend (['-crab-log', l])

        # pick out extra seahorn/crab options
        argv.extend (list(filter (_is_seahorn_opt, extra)))

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

class InspectBitcode(sea.LimitedCmd):
    def __init__ (self, quiet=False):
        super (InspectBitcode, self).__init__ ('inspect-bitcode', allow_extra=True)
        self.help = 'Utilities for program inspection'

    @property
    def stdout (self):
        return self.seainspectCmd.stdout

    def mk_arg_parser (self, ap):
        ap = super (InspectBitcode, self).mk_arg_parser (ap)
        add_in_out_args (ap)
        ap.add_argument ('--profiler', default=False, action='store_true',
                         dest='profiling',
                         help='Print number of functions, blocks, instructions, etc')
        ap.add_argument ('--cfg-dot', default=False, action='store_true',
                         dest='cfg_dot',
                         help='Print CFG of all functions to dot format')
        ap.add_argument ('--cfg-only-dot', default=False, action='store_true',
                         dest='cfg_only_dot',
                         help='Print CFG of all functions (without instructions) to dot format')
        ap.add_argument ('--sea-dsa',
                         help="Choose the SeaDsa analysis: "
                         "flat (flat memory), "
                         "ci (context-insensitive), "
                         "ci-types (context-insensitive, type-sensitive), "
                         "cs (context-sensitive),"
                         "cs-types (context-sensitive, type-sensitive), "
                         "cs-vcgen (context-sensitive for VC generation), "
                         "cs-vcgen-types (context-sensitive for VC generation, type-sensitive)",
                         choices=['flat','ci','ci+t','cs','cs+t','cs-vcgen','cs-vcgen+t'],
                         dest='sea_dsa', default='cs+t')
        ap.add_argument ('--mem-dot', default=False, action='store_true',
                         dest='mem_dot',
                         help='Print SeaDsa memory graphs of alls functions to dot format')
        ap.add_argument ('--mem-callgraph-dot', default=False, action='store_true',
                         dest='mem_cg_dot',
                         help='Print SeaDsa call graph to dot format')
        ap.add_argument ('--mem-callgraph-stats', default=False, action='store_true',
                         dest='mem_cg_stats',
                         help='Print stats about SeaDsa call graph resolution')
        ap.add_argument ('--mem-stats', default=False, action='store_true',
                         dest='mem_stats', help='Print stats about all SeaDsa memory graphs')
        ap.add_argument ('--mem-smc-stats', default=False, action='store_true',
                         dest='smc_stats', help='Print stats collected by our Simple Memory Checker')
        ap.add_argument ('--mem-dot-outdir', default="", type=str, metavar='DIR',
                         dest='dot_outdir', help='Directory to store all dot files generated by SeaDsa')
        ap.add_argument ('--cha', default=False, action='store_true',
                         dest='cha', help='Print results of the Class Hierarchy Analysis (for C++) (very experimental)')
        return ap

    def run (self, args, extra):
        cmd_name = which ('seainspect')
        if cmd_name is None: raise IOError ('seainspect not found')
        self.seainspectCmd = sea.ExtCmd (cmd_name,'',quiet)

        argv = list()

        use_sea_dsa = args.mem_stats or args.smc_stats or args.mem_cg_stats or \
                      args.mem_cg_dot or args.mem_dot

        if args.profiling: argv.extend(['-profiler'])

        if args.cfg_dot: argv.extend(['-cfg-dot'])
        if args.cfg_only_dot: argv.extend(['-cfg-only-dot'])

        if use_sea_dsa:
            print("Selected sea-dsa analysis: " + str(args.sea_dsa))
            if args.sea_dsa == 'flat':
                argv.extend (['--sea-dsa=flat'])
            elif args.sea_dsa == 'ci' or args.sea_dsa == 'ci+t':
                argv.extend (['--sea-dsa=ci'])
            elif args.sea_dsa == 'cs' or args.sea_dsa == 'cs+t':
                argv.extend (['--sea-dsa=butd-cs'])
            elif args.sea_dsa == 'cs-vcgen' or args.sea_dsa == 'cs-vcgen+t':
                argv.extend (['--sea-dsa=cs'])
            else:
                assert(False)
            if args.sea_dsa == 'ci+t' or \
               args.sea_dsa == 'cs+t' or \
               args.sea_dsa == 'cs-vcgen+t':
                argv.extend(['-sea-dsa-type-aware'])

        if args.mem_stats:
            argv.extend(['-mem-stats'])

        if args.mem_cg_stats:
            argv.extend(['--mem-callgraph-stats'])

        if args.smc_stats:
            argv.extend(['--mem-smc-stats'])
            argv.extend(['--smc-analyze-only'])
            argv.extend(['--print-smc-stats'])

        if args.mem_dot or args.mem_cg_dot:
            if args.mem_dot:
                argv.extend(['-mem-dot'])
            if args.mem_cg_dot:
                argv.extend(['-mem-callgraph-dot'])
            if args.dot_outdir != "":
                argv.extend(['-sea-dsa-dot-outdir={0}'.format(args.dot_outdir)])

        if args.cha: argv.extend (['-cha'])

        argv.extend (args.in_files)
        # pick out extra seahorn/crab options
        argv.extend (list(filter (_is_seahorn_opt, extra)))

        return self.seainspectCmd.run (args, argv)

class SeaExeCex(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super (SeaExeCex, self).__init__('exe-cex',
                                         'Executable Counterexamples',
                                         allow_extra=True)
    @property
    def stdout (self):
        return

    def name_out_file (self, in_files, args=None, work_dir=None):
        return _remap_file_name (in_files[0], '.exe', work_dir)

    def mk_arg_parser (self, ap):
        ap = super (SeaExeCex, self).mk_arg_parser (ap)
        add_tmp_dir_args (ap)
        add_in_out_args (ap)
        _add_S_arg (ap)
        ap.add_argument ('--harness', '-harness',
                         dest='harness',
                         help='Destination file for the harness',
                         default=None, metavar='FILE')
        ap.add_argument ('--bit-precise','-bit-precise',
                         dest='bv_cex',
                         help='Generate bit-precise counterexamples',
                         default=False, action='store_true')
        ap.add_argument ('--bit-mem-precise','-bit-mem-precise',
                         dest='bv_part_mem',
                         help='Generate bit- and memory-precise counterexamples',
                         default=False, action='store_true')
        ap.add_argument ('--alloc-mem', '-alloc-mem',
                         default=False, action='store_true',
                         dest='alloc_mem',
                         help='Allocate space for uninitialized memory')
        ap.add_argument ('--verify', '-verify',
                         default=False, action='store_true',
                         dest='verify',
                         help='Verify the harness executes __VERIFIER_error')
        return ap

    def run(self, args, extra):
        # FIXME: the -o is used both `sea pf` and `sea exe`. Thus,
        # the output of `sea pf` is overwritten by the output of `sea exe`.
        try:
            harness_file = args.harness
            if harness_file is None:
                harness_file = 'harness.ll'

            if args.out_file is None:
                args.out_file = 'harness'

            try:
                os.remove(harness_file)
            except OSError:
                pass

            ## `sea pf`: find counterexample and generate harness
            c = sea.SeqCmd('','',
                           [Clang(), Seapp(), MixedSem(), Seaopt(), \
                            Seahorn(solve=True)])
            argv = list ()
            argv.extend(['-m64', '-g'])
            argv.extend(extra)
            # TODO: we should remove from `extra` the following options:
            argv.extend(['--cex={0}'.format(harness_file)])
            if args.bv_cex or args.bv_part_mem:
                argv.extend(['--bv-cex'])
            if args.bv_part_mem:
                argv.extend(['--horn-bv-part-mem'])
            res = c.run(args,  argv)
            if res != 0:
                print('\n\nThe harness was not generated. Aborting ...\n');
                return res

            if not os.path.isfile(harness_file): # if program was safe
                print('\n\nThe harness was not generated. Aborting ...\n');
                # remove the .smt2 file
                try:
                    os.remove(args.out_file)
                except OSError:
                    pass
                # some error code different from 0
                return 1


            ## `sea exe`: generate executable
            c = sea.SeqCmd('','',
                           [Clang(), Seapp(strip_extern=True,keep_lib_fn=True), \
                            Seapp(internalize=True), WrapMem(), LinkRt()])
            argv = list()
            argv.extend(['-m64', '-g'])
            argv.extend(extra)
            # TODO: we should remove from `extra` the following options:
            if args.alloc_mem:
                argv.extend(['--alloc-mem'])
            infiles = args.in_files
            infiles.extend([harness_file])
            res = c.run(args, argv)
            if res != 0:
                print('\n\nThe executable counterexample was not generated. Aborting ...\n');
            else:
                print ('\n\nGenerated executable counterexample {0}'.format(args.out_file))

            # Optionally verify the harness reaches __VERIFIER_error
            if res == 0 and args.verify:
                args.in_files = [args.out_file]
                c = ExecHarness()
                c.run(args, [])

            return res

        except Exception as e:
            raise IOError(str(e))

## SeaHorn aliases
FrontEnd = sea.SeqCmd ('fe', 'Front end: alias for clang|pp|ms|opt',
                       [Clang(), Seapp(), MixedSem(), Seaopt ()])
Smt = sea.SeqCmd ('smt', 'alias for fe|horn', FrontEnd.cmds + [Seahorn()])
Clp = sea.SeqCmd ('clp', 'alias for fe|horn-clp', FrontEnd.cmds + [SeahornClp()])
Boogie= sea.SeqCmd ('boogie', 'alias for fe|horn --boogie',
                    FrontEnd.cmds + [Seahorn(solve=False,enable_boogie=True)])
Pf = sea.SeqCmd ('pf', 'alias for fe|horn --solve',
                 FrontEnd.cmds + [Seahorn(solve=True)])
LfeSmt = sea.SeqCmd ('lfe-smt', 'alias for lfe|horn', [LegacyFrontEnd(), Seahorn()])
LfeClp= sea.SeqCmd ('lfe-clp', 'alias for lfe|horn-clp', [LegacyFrontEnd(), SeahornClp()])
BndSmt = sea.SeqCmd ('bnd-smt', 'alias for fe|unroll|cut-loops|ms|opt|horn',
                     FrontEnd.cmds + [Unroll(), CutLoops(), MixedSem (),
                                      Seaopt(), Seahorn()])
BndFrontEnd = sea.SeqCmd('bnd-fe', 'Bounded front-end: alias for fe|unroll|cut-loops|opt',
                         FrontEnd.cmds + [Unroll(), CutLoops(), Seaopt()])
Bpf = sea.SeqCmd ('bpf', 'alias for fe|unroll|cut-loops|opt|horn --solve',
                  FrontEnd.cmds + [Unroll(), CutLoops(), Seaopt(), Seahorn(solve=True)])
Crab = sea.SeqCmd ('crab', 'alias for fe|crab-inst', FrontEnd.cmds + [CrabInst()])
seaTerm = sea.SeqCmd ('term', 'SeaHorn Termination analysis', Smt.cmds + [SeaTerm()])
ClangPP = sea.SeqCmd ('clang-pp', 'alias for clang|pp', [Clang(), Seapp()])
seaIncSmt = sea.SeqCmd ('inc-smt', 'alias for fe|horn|inc. ' +
                        'It should be used only as a helper by sea_inc.',
                        Smt.cmds + [SeaInc()])
Ndc = sea.SeqCmd ('ndc', 'alias for fe|ndc-inst',
                  [Clang(), Seapp(), NdcInst(), MixedSem(), Seaopt(), Seahorn(solve=True)])
Exe = sea.SeqCmd ('exe', 'alias for clang|pp --strip-extern|pp --internalize|wmem|rmtf|linkrt',
                  [Clang(), Seapp(strip_extern=True,keep_lib_fn=True),
                   Seapp(internalize=True), WrapMem(), RemoveTargetFeatures(), LinkRt()])
Inspect = sea.SeqCmd ('inspect', 'alias for fe + inspect-bitcode', FrontEnd.cmds + [InspectBitcode()])
Smc = sea.SeqCmd ('smc', 'alias for fe|opt|smc',
                   [Clang(), Seapp(), SimpleMemoryChecks(), MixedSem(),
                    Seaopt(), Seahorn(solve=True)])
Fpf = sea.SeqCmd('fpf', 'fat-bnd-check|fe|unroll|cut-loops|opt|horn --solve', 
                 [FatBoundsCheck()] + FrontEnd.cmds + [Unroll(), CutLoops(), Seaopt(), Seahorn(solve=True)])
