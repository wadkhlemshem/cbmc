import sys
import subprocess
import math

ranges={
  "--program-only": [],
  "--function": ["something-wrong", "main"],
  "--preprocess": [],
  "--no-simplify": [],
  "--unwind": ["something-wrong", "-1", "0", "3", "4294967296"],
  "--unwindset": ["something-wrong", "something-wrong:-1", "something-wrong:4294967296"],
  "--slice-formula": [],
  "--full-slice": [],
  "--debug-level": ["something-wrong", "-1", "0", "4294967296"],
  "--no-propagation": [],
  "--no-simplify-if": [],
  "--document-subgoals": [],
  "--outfile": ["some-file.txt", "some-wrong-dir/some-file.txt"],
  "--test-preprocessor": [],
  "--D": ["some-file.txt", "some-wrong-dir/some-file.txt"],
  "--I": ["some-file.txt", "some-wrong-dir/some-file.txt"],
  "--c89": [],
  "--c99": [],
  "--c11": [],
  "--cpp89": [],
  "--cpp99": [],
  "--cpp11": [],
  "--classpath": ["some-file.txt", "some-wrong-dir/some-file.txt"],
  "--cp": ["some-file.txt", "some-wrong-dir/some-file.txt"],
  "--slice-by-trace": ["some-file.txt", "some-wrong-dir/some-file.txt"],
  "--main-class": ["something-wrong"],
  "--depth):": [],
  "--partial-loops": [],
  "--no-unwinding-assertions": [],
  "--unwinding-assertions": [],
  "--no-assertions": [],
  "--no-assumptions": [],
  "--no-built-in-assertions": [],
  "--xml-ui": [],
  "--xml-interface": [],
  "--json-ui": [],
  "--smt1": [],
  "--smt2": [],
  "--fpa": [],
  "--cvc3": [],
  "--cvc4": [],
  "--boolector": [],
  "--yices": [],
  "--z3": [],
  "--opensmt": [],
  "--mathsat": [],
  "--no-sat-preprocessor": [],
  "--no-pretty-names": [],
  "--beautify": [],
  "--dimacs": [],
  "--refine": [],
  "--max-node-refinement": ["something-wrong", "-1", "0", "1", "4294967296"],
  "--refine-arrays": [],
  "--refine-arithmetic": [],
  "--aig": [],
  "--16": [],
  "--32": [],
  "--64": [],
  "--LP64": [],
  "--ILP64": [],
  "--LLP64": [],
  "--ILP32": [],
  "--LP32": [],
  "--little-endian": [],
  "--big-endian": [],
  "--show-goto-functions": [],
  "--show-loops": [],
  "--show-symbol-table": [],
  "--show-parse-tree": [],
  "--show-vcc": [],
  "--show-claims": [],
  "--claim": ["something-wrong"],
  "--show-properties": [],
  "--drop-unused-functions": [],
  "--property": ["something-wrong"],
  "--stop-on-fail": [],
  "--trace": [],
  "--error-label": ["something-wrong"],
  "--verbosity": ["something-wrong", "-1", "0", "4294967296"],
  "--no-library": [],
  "--nondet-static": [],
  "--version": [],
  "--cover": ["something-wrong", "location", "branch", "condition", "decision", "path", "MCDC", "assertion", "cover instruction"],
  "--symex-coverage-report": ["some-file.txt", "some-wrong-dir/some-file.txt"],
  "--mm": ["something-wrong", "sc", "tso", "pso", "rmo", "power"],
  "--i386-linux": [],
  "--i386-macos": [],
  "--i386-win32": [],
  "--win32": [],
  "--winx64": [],
  "--gcc": [],
  "--ppc-macos": [],
  "--unsigned-char": [],
  "--arrays-uf-always": [],
  "--arrays-uf-never": [],
  "--string-abstraction": [],
  "--no-arch": [],
  "--arch": ["something-wrong", "none", "alpha", "arm64", "armel", "armhf", "arm", "mips64el","mipsn32el", "mipsel", "mips64", "mipsn32", "mips", "powerpc", "ppc64", "ppc64le", "sparc", "sparc64", "ia64", "s390x", "s390", "x32", "v850", "hppa", "sh4", "x86_64", "i386"],
  "--round-to-nearest": [],
  "--round-to-plus-inf": [],
  "--round-to-minus-inf": [],
  "--round-to-zero": [],
  "--graphml-witness": ["some-file.txt", "some-wrong-dir/some-file.txt"], 
  "--java-max-vla-length": ["something-wrong", "-1", "0", "1", "5", "4294967296"],
  "--java-unwind-enum-static": [],
  "--java-cp-include-files": ["some-file.txt", "some-wrong-dir/some-file.txt"], 
  "--localize-faults": [],
  "--localize-faults-method": ["something-wrong"],
  "--lazy-methods": [],
  "--fixedbv": [],
  "--floatbv": [],
  "--all-claims": [],
  "--all-properties": [],
  "--bounds-check": [],
  "--pointer-check": [],
  "--memory-leak-check": [],
  "--div-by-zero-check": [],
  "--signed-overflow-check": [],
  "--unsigned-overflow-check": [],
  "--pointer-overflow-check": [],
  "--conversion-check": [],
  "--undefined-shift-check": [],
  "--float-overflow-check": [],
  "--nan-check": [],
  "--no-built-in-assertions": []
  }

timeout=2
cmd=sys.argv[1]
benchmark=sys.argv[2]
expected=[0, 6, 7, 10, 64, 124]

# build extended option set
all_options=[]
for p, r in ranges.items():
    if r == []:
        all_options.append(p)
    else:    
        for v in r:
            all_options.append(p+" "+v)

# exhaustive enumeration of all option combinations
for c in range(0, int(math.pow(2, len(all_options)))):
    i = c
    options = []
    for o in all_options:
        if i & 1 == 1:
            options.append(o)
        i = i >> 1

    command=" ".join([cmd, benchmark] + options)

    process = subprocess.Popen(
        "timeout "+str(timeout)+" "+command,
        cwd="./",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        shell=True,
        executable="/bin/bash")
    process.communicate()

    if not process.returncode in expected:
        print("FAIL("+str(process.returncode)+")\t"+command)
    else:
        print("OK("+str(process.returncode)+")\t"+command)
