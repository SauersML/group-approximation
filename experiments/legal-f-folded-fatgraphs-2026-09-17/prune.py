"""Prune a vcg.py / cg_memory.py column dump to the support of the last master solution (x > tol), the columns
added after it (not yet in the master), and (optionally) the TAIL most recently generated columns, for a faster
reload with --load.  Pruning only drops columns: the reloaded master is a restriction, and every certificate is
checked afresh by farkas_vmem.py, so pruning cannot affect soundness.
usage: python3 prune.py dump.json out.json [tol] [tail]"""
import sys, json
import numpy as np
J = json.load(open(sys.argv[1])); tol = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-9
tail = int(sys.argv[4]) if len(sys.argv) > 4 else 0
x = np.array(J["x"]); ci = np.array(J["colidx"]); n = len(J["columns"])
keep = [P for i, (P, j) in enumerate(zip(J["columns"], ci)) if j >= len(x) or x[j] > tol or i >= n - tail]
json.dump({"columns": keep, "pruned_from": sys.argv[1], "tol": tol, "tail": tail}, open(sys.argv[2], "w"))
print("kept", len(keep), "of", n)
