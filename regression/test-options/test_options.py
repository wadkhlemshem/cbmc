import sys
import subprocess
import math

ranges=[]
positive_rules=["--show-goto-functions", "--no-simplify", "--show-loops"]
negitive_rules=[]

timeout=2
cmd=sys.argv[1]
benchmark=sys.argv[2]
expected=[0, 6, 10, 64, 124]

for c in range(0, int(math.pow(2, len(positive_rules)))):
    i = c
    options = []
    for o in positive_rules:
        if i & 1 == 1:
            options.append(o)
        i = i >> 1

    command=" ".join([cmd, benchmark] + options)
    print(" ".join(options))

    process = subprocess.Popen(
        "timeout "+str(timeout)+" "+command,
        cwd="./",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        shell=True,
        executable="/bin/bash")
    process.communicate()

    print(str(process.returncode))

    if not process.returncode in expected:
        print("FAIL")
    else:
        print("OK")
