"""DRAT certificate that the fixed 1/3 barrier of third_barrier.py is unrealizable on B_n:
no E subset B_n has w(X_E(g)) >= 1/3 for all g in I_n.  Glucose4 proof trace + drat-trim.
usage: python3 certify_barrier.py {F|F2|Z2} n drat_trim_binary
"""
import json
import subprocess
import sys

from pysat.formula import CNF
from pysat.solvers import Glucose4

from ramsey_sat import setup
from third_barrier import FAM


def main(name, n, drat):
    dist, idx, interior, k = setup(name, n)
    forb = [P for P in range(1 << k) if P not in FAM]
    cnf = CNF()
    for row in interior:
        for P in forb:
            cnf.append([(-v if P >> i & 1 else v) for i, v in enumerate(row)])
    base = f"certify_barrier_{name}_n{n}"
    cnf.to_file(base + ".cnf")
    s = Glucose4(bootstrap_with=cnf.clauses, with_proof=True)
    sat = s.solve()
    assert not sat
    with open(base + ".drat", "w") as f:
        for line in s.get_proof():
            f.write(line + "\n")
        f.write("0\n")
    s.delete()
    out = subprocess.run([drat, base + ".cnf", base + ".drat", "-w"], capture_output=True,
                         text=True, timeout=6000)
    rec = {"group": name, "n": n, "ball": len(dist), "interior": len(interior),
           "family": FAM, "cnf_clauses": len(cnf.clauses), "unsat": not sat,
           "drat_verified": "s VERIFIED" in out.stdout,
           "drat_tail": out.stdout.strip().splitlines()[-3:]}
    json.dump(rec, open(base + ".json", "w"), indent=1)
    print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3])
