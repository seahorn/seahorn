#!/usr/bin/python

from sys import argv, maxsize, exit
from subprocess import Popen, PIPE

if len(argv) < 3:
    exit(1)
harness_opt, exe_opt, code, pf_args = argv[1], argv[2], argv[3], argv[4:]

m32_or_m64 = "-m64" if maxsize > 2**32 else "-m32"
output, _ = Popen(["sea", "pf", "--cex=%s" % harness_opt, m32_or_m64, code] + pf_args, stdout=PIPE).communicate()

if "sat" in output.split("\n"):
    print("sat")
    Popen(["sea", "exe", m32_or_m64, "-g", code, harness_opt, "-o", exe_opt]).communicate()
    expected_error, _ = Popen(exe_opt, stdout=PIPE).communicate()
    print(expected_error)
elif "unsat" in output.split("\n"):
    print("unsat")
else:
    print(output)
