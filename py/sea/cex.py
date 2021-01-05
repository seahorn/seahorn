import sys
import os
import subprocess
import sea
import sea.commands

from sea import add_in_args, add_in_out_args, add_tmp_dir_args
from sea.commands import _remap_file_name, _add_S_arg, Clang, Seapp, WrapMem, \
    RemoveTargetFeatures, LinkRt, MixedSem, Seaopt, Seahorn


'''
Set of commands for executable counterexample functionality
'''


class CexGen(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(CexGen, self).__init__("cex",
                                     'Generate Counter-example executable from harness',
                                     allow_extra=True)
        self.clangCmd = None

    @property
    def stdout(self):
        return self.clangCmd.stdout

    def name_out_file(self, in_files, args=None, work_dir=None):
        return _remap_file_name(in_files[0], '', work_dir)

    def mk_arg_parser(self, ap):
        ap = super(CexGen, self).mk_arg_parser(ap)
        add_tmp_dir_args(ap)
        add_in_out_args(ap)
        _add_S_arg(ap)

        ap.add_argument('--run', '-run', dest='run',
                        help='Run generated executable',
                        default=False, action='store_true')
        ap.add_argument('--klee-internalize', '-klee-internalize',
                        dest='internalize',
                        help='Apply klee internalize pre-processing',
                        default=False, action='store_true')
        ap.add_argument('--only-strip-extern', '-only-strip-extern',
                        dest='strip_extern',
                        help='Strip external functions during internalize pre-processing',
                        default=False, action='store_true')
        ap.add_argument('--keep-lib-fn', '-keep-lib-fn',
                        dest='keep_lib_fn',
                        help='Keep lib functions during internalize pre-processing',
                        default=False, action='store_true')
        ap.add_argument('--wrap-mem', '-wrap-mem',
                        dest='wrapmem',
                        help='Wrap memory read/access instructions',
                        default=False, action='store_true')
        ap.add_argument('--rmtf', '-rmtf',
                        dest='rmtf',
                        help='Remove target features for cross platform files',
                        default=False, action='store_true')
        ap.add_argument('-m', type=int, dest='machine',
                        help='Machine architecture MACHINE:[32,64]',
                        default=32)
        return ap

    def run(self, args, extra):
        cmds = [Clang()]
        # following logic in Seapp, where klee internalize is separate
        if args.strip_extern:
            pp = Seapp(strip_extern=True, keep_lib_fn=args.keep_lib_fn)
            cmds.append(pp)
        if args.internalize:
            cmds.append(Seapp(internalize=True))

        if args.wrapmem:
            cmds.append(WrapMem())

        if args.rmtf:
            cmds.append(RemoveTargetFeatures())

        if args.out_file is None:
            target = os.path.basename(args.in_files[0]).split(sep='.')[0]
            args.out_file = "/tmp/{}_debug.exe".format(target)

        linkRtCmd = LinkRt()
        self.clangCmd = linkRtCmd
        cmds.append(linkRtCmd)

        pipeline = sea.SeqCmd('', '', cmds)
        argv = ["-m{}".format(args.machine), '-g']  # debug info is a must
        argv.extend(extra)
        res = pipeline.run(args, argv)
        if res:
            print("Executable Counterexample generation failed... \n")
        else:
            print("Generated executable counterexample: %s" %
                  str(args.out_file))
            if args.run:
                print("Running executable counterexample: \n")
                args.in_files = [args.out_file]
                c = ExecHarness()
                c.run(args, [])


class ExecHarness(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(ExecHarness, self).__init__('exec-harness', 'Execute an executable harness to see if it calls __VERIFIER_error',
                                          allow_extra=True)
        self.harnessCmd = None

    @property
    def stdout(self):
        return self.harnessCmd.stdout

    def mk_arg_parser(self, ap):
        ap = super(ExecHarness, self).mk_arg_parser(ap)
        add_in_args(ap)
        return ap

    def run(self, args, extra):
        if len(args.in_files) != 1:
            raise IOError(
                'ExecHarness expects the harness executable as an input')
        eharness = os.path.abspath(args.in_files[0])

        self.harnessCmd = sea.ExtCmd(eharness)
        if args.cpu is None:
            args.cpu = 10

        retval = self.harnessCmd.run(
            args, [], encoding='utf-8', errors='replace', stdout=subprocess.PIPE)

        if "[sea] __VERIFIER_error was executed" in self.harnessCmd.stdout:
            print("__VERIFIER_error was executed")
        else:
            print("__VERIFIER_error was not executed")

        return retval


class SeaExeCex(sea.LimitedCmd):
    def __init__(self, quiet=False):
        super(SeaExeCex, self).__init__('exe-cex',
                                        'Executable Counterexamples',
                                        allow_extra=True)

    @property
    def stdout(self):
        return

    def name_out_file(self, in_files, args=None, work_dir=None):
        return _remap_file_name(in_files[0], '.exe', work_dir)

    def mk_arg_parser(self, ap):
        ap = super(SeaExeCex, self).mk_arg_parser(ap)
        add_tmp_dir_args(ap)
        add_in_out_args(ap)
        _add_S_arg(ap)
        ap.add_argument('--harness', '-harness',
                        dest='harness',
                        help='Destination file for the harness',
                        default=None, metavar='FILE')
        ap.add_argument('--bit-precise', '-bit-precise',
                        dest='bv_cex',
                        help='Generate bit-precise counterexamples',
                        default=False, action='store_true')
        ap.add_argument('--bit-mem-precise', '-bit-mem-precise',
                        dest='bv_part_mem',
                        help='Generate bit- and memory-precise counterexamples',
                        default=False, action='store_true')
        ap.add_argument('--alloc-mem', '-alloc-mem',
                        default=False, action='store_true',
                        dest='alloc_mem',
                        help='Allocate space for uninitialized memory')
        ap.add_argument('--verify', '-verify',
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
            c = sea.SeqCmd('', '',
                           [Clang(), Seapp(), MixedSem(), Seaopt(),
                            Seahorn(solve=True)])
            argv = list()
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
                print('\n\nThe harness was not generated. Aborting ...\n')
                return res

            if not os.path.isfile(harness_file):  # if program was safe
                print('\n\nThe harness was not generated. Aborting ...\n')
                # remove the .smt2 file
                try:
                    os.remove(args.out_file)
                except OSError:
                    pass
                # some error code different from 0
                return 1

            ## `sea exe`: generate executable
            c = sea.SeqCmd('', '',
                           [Clang(), Seapp(strip_extern=True, keep_lib_fn=True),
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
                print(
                    '\n\nThe executable counterexample was not generated. Aborting ...\n')
            else:
                print('\n\nGenerated executable counterexample {0}'.format(
                    args.out_file))

            # Optionally verify the harness reaches __VERIFIER_error
            if res == 0 and args.verify:
                args.in_files = [args.out_file]
                c = ExecHarness()
                c.run(args, [])

            return res

        except Exception as e:
            raise IOError(str(e))
