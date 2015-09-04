import argparse
import textwrap
import json
import csv
#import matplotlib.pyplot as plt
#from mpl_toolkits.mplot3d import Axes3D
import numpy

def cc_sv15(_f, print_ko, print_err):
    bench_data = {}
    with open(_f, 'rb') as csvfile:
        reader = csv.DictReader(csvfile)
        solved, total_bench, safe, unsafe, unsound_safe, unsound_unsafe = 0, 0, 0, 0, 0, 0
        timeout, segfault, various, memory_out = 0, 0, 0, 0
        for row in reader:
            total_bench +=1
            if row['Result'] == "TRUE":
                if 'true' in row['base']:
                    safe +=1
                    bench_data.update({row['base']: row['Cpu']})
                else:
                    unsound_unsafe +=1
                    if print_ko: print row['File'] + " " + row['Result'] + ' --> KO'
            if row['Result'] == "FALSE":
                if 'false' in row['base']:
                    unsafe +=1
                    bench_data.update({row['base']: row['Cpu']})
                else:
                    unsound_safe +=1
                    if print_ko: print row['File'] + " " + row['Result'] + ' --> KO'
            if row["Status"] == "0":
                solved += 1
            if row["Status"] == "9":
                if print_err: print row['File']  + ' --> TIMEOUT'
                timeout += 1
            if row["Status"] == "-6":
                if print_err: print row['File']  + ' --> SEGFAULT'
                segfault += 1
            if row["Status"] == "-11":
                if print_err: print row['File']  + ' --> MEMORY-OUT'
                memory_out += 1
            if row["Status"] not in ["0", "9", "-6", "-11"]:
                if print_err: print row['File']  + " | Status: " +  row["Status"] + '| --> VARIOUS'
                various +=1
    print "\n\n==========SUMMARY [ " +  _f  + " ]=========="
    print "TOTAL N. BENCHMARK: " + str(total_bench)
    print "SOLVED : " + str(solved)
    print "UNSOUND (SAFE -> UNSAFE): " + str(unsound_safe)
    print "UNSOUND (UNSAFE -> SAFE): " + str(unsound_unsafe)
    print "ERROR SEGFAULT: " + str(segfault)
    print "ERROR TIMEOUT: " + str(timeout)
    print "ERROR MEMORY-OUT: " + str(memory_out)
    print "ERROR VARIOUS: " + str(various)
    print "==============================="




def cc_sv14(_f, print_ko, print_err):
    bench_data = {}
    with open(_f, 'rb') as csvfile:
        reader = csv.DictReader(csvfile)
        err,unsafe,safe, total_bench, unsound_safe, unsound_unsafe = 0, 0, 0, 0, 0, 0
        timeout, segfault, various, memory_out = 0, 0, 0, 0
        solved_safe = []
        solved_unsafe = []
        unsolved = []
        for row in reader:
            total_bench +=1
            if row['Result'] == "SAFE":
                if 'true' in row['base']:
                    safe +=1
                    solved_safe.append(row["base"])
                    bench_data.update({row['base']: row['Cpu']})
                else:
                    unsound_unsafe +=1
                    if print_ko: print row['File'] + " " + row['Result'] + ' --> KO'
            if row['Result'] == "UNSAFE":
                if 'false' in row['base']:
                    unsafe +=1
                    solved_unsafe.append(row["base"])
                    bench_data.update({row['base']: row['Cpu']})
                else:
                    unsound_safe +=1
                    if print_ko: print row['File'] + " " + row['Result'] + ' --> KO'
            if row['Result'] == "ERR":
                err +=1
                bench_data.update({row['base']: '50'})
            if row["Status"] == "-9":
                if print_err: print row['File']  + ' --> TIMEOUT'
                timeout += 1
            if row["Status"] == "-6":
                if print_err: print row['File']  + ' --> SEGFAULT'
                segfault += 1
            if row["Status"] == "-11":
                if print_err: print row['File']  + ' --> MEMORY-OUT'
                memory_out += 1
            if row["Result"] == "ERR" and (row["Status"] == "0" or row["Status"] == "1"):
                if print_err: print row['File']  + ' --> VARIOUS'
                various += 1
    print "\n\n==========SUMMARY (Consistency checker) of [ " +  _f  + " ]=========="
    print "TOTAL N. BENCHMARK: " + str(total_bench)
    print "SOLVED SAFE : " + str(safe)
    print "SOLVED UNSAFE : " + str(unsafe)
    print "NOT SOLVED: " + str(err)
    print "UNSOUND (SAFE -> UNSAFE): " + str(unsound_safe)
    print "UNSOUND (UNSAFE -> SAFE): " + str(unsound_unsafe)
    print "ERROR SEGFAULT: " + str(segfault)
    print "ERROR TIMEOUT: " + str(timeout)
    print "ERROR MEMORY-OUT: " + str(memory_out)
    print "ERROR VARIOUS: " + str(various)
    print "==============================="
    return bench_data, solved_safe, solved_unsafe


def plot(data, _f):
    for k,v in data.iteritems():
        print "\n\n======== PLOTTING ======="
        print "EXPERIMENTS NAME : " + k
        runtimes = []
        for b,r in v.iteritems(): runtimes.append(float(r))
        print "RUNTIMES MEAN VALUE : " + str(numpy.mean(runtimes))
        print "========================"


def solved_analysis(data, _f):
    print "... solved benchmarks analysis"
    print "SOLVED BY BOTH (SAFE): " + str(len(set(data["large_step_solved"]).intersection(set(data["crab_large_solved"]))))
    print "SOLVED BY BOTH (UNSAFE): " + str(len(set(data["large_step_unsolved"]).intersection(set(data["crab_large_unsolved"]))))
    print "SOLVED BY LARGE AND NOT BY CRAB (SAFE): " + str(len(set(data["large_step_solved"]).difference(set(data["crab_large_solved"]))))
    print "SOLVED BY CRAB AND NOT BY LARGE (SAFE): " + str(len(set(data["crab_large_solved"]).difference(set(data["large_step_solved"]))))
    print "SOLVED BY LARGE AND NOT BY CRAB (UNSAFE): " + str(len(set(data["large_step_unsolved"]).difference(set(data["crab_large_unsolved"]))))
    print "SOLVED BY CRAB AND NOT BY LARGE (SAFE): " + str(len(set(data["crab_large_unsolved"]).difference(set(data["large_step_unsolved"]))))



if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog='Seahorn Utils',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=textwrap.dedent('''\
                   Seahorn Utils
            --------------------------------
            '''))
    parser.add_argument('-csv', '--csv', required=False, dest="csv", nargs="*")
    parser.add_argument('-cc', '--cc', required=False, dest="cc", action="store_true")
    parser.add_argument('-plot', '--plot', required=False, dest="plot", action="store_true")
    parser.add_argument('-exp', '--exp', required=False, dest="exp", nargs="*")
    parser.add_argument('-ko', '--ko', required=False, dest="ko", action="store_true")
    parser.add_argument('-err', '--err', required=False, dest="err", action="store_true")
    parser.add_argument('-solved', '--solved', required=False, dest="solved", action="store_true")
    parser.add_argument('-sv15', '--sv15', required=False, dest="sv15", action="store_true")
    args = parser.parse_args()
    _csv = args.csv # csv file lists
    _exp = args.exp # names of experimental data
    if args.plot:
        assert len(_exp) == len(_csv)  # names and file lists has to be the same
    try:
        solved_data = {}
        if _csv:
            all_data = {}
            i = 0
            for _f in _csv:
                if args.sv15:
                    cc_sv15(_f, args.ko, args.err)
                else:
                    bench_data, solved_safe, solved_unsafe = cc_sv14(_f, args.ko, args.err)
                    if args.plot:
                        all_data.update({_exp[i] : bench_data})
                        i += 1
                    elif args.solved:
                        s = _exp[i]+"_solved"
                        u = _exp[i]+"_unsolved"
                        solved_data.update({ s : solved_safe})
                        solved_data.update({ u : solved_unsafe})
                        i += 1
        if args.plot:
            plot(all_data, _f)
        elif args.solved:
            solved_analysis(solved_data, _f)
    except Exception as e:
        print str(e)
