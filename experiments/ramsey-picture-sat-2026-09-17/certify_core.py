"""Certify the obstruction of barrier_core.py: the rows of barrier_core_{G}_n{n}.json alone
already force "X_E(g) in Y_w for every listed g" to be UNSAT (Glucose4 proof, checked by
drat-trim), and the set is irreducible: dropping any one row gives a SAT instance, whose
model is re-checked directly (every listed picture lies in Y_w).  Also asserts that the mask
list FAM is exactly {P : w(P) >= 1/3}.
usage: python3 certify_core.py {F|F2|Z2} n drat_trim_binary
"""
import json
import subprocess
import sys

from pysat.formula import CNF
from pysat.solvers import Glucose4

from ramsey_sat import setup
from third_barrier import FAM, THR, wP


def clauses(rows, k):
    forb = [P for P in range(1 << k) if P not in FAM]
    return [[(-v if P >> i & 1 else v) for i, v in enumerate(row)] for row in rows for P in forb]


def main(name, n, drat):
    # Y_w is exactly {P : w(P) >= 1/3} (32 cases, exact)
    assert sorted(FAM) == [P for P in range(32) if wP(P) >= THR]
    core = json.load(open(f"barrier_core_{name}_n{n}.json"))
    dist, idx, interior, k = setup(name, n)
    rows = [interior[r] for r in core["rows"]]
    cnf = CNF(from_clauses=clauses(rows, k))
    base = f"certify_core_{name}_n{n}"
    cnf.to_file(base + ".cnf")
    s = Glucose4(bootstrap_with=cnf.clauses, with_proof=True)
    assert not s.solve()
    with open(base + ".drat", "w") as f:
        for line in s.get_proof():
            f.write(line + "\n")
        f.write("0\n")
    s.delete()
    out = subprocess.run([drat, base + ".cnf", base + ".drat", "-w"], capture_output=True,
                         text=True, timeout=600)
    irreducible = True
    for j in range(len(rows)):
        sub = rows[:j] + rows[j + 1:]
        t = Glucose4(bootstrap_with=clauses(sub, k))
        ok = t.solve()
        model = {abs(l): l > 0 for l in t.get_model()} if ok else None
        t.delete()
        if not ok or not all(sum(1 << i for i, v in enumerate(row) if model.get(v, False)) in FAM
                             for row in sub):
            irreducible = False
    rec = {"group": name, "n": n, "core_rows": len(rows), "cnf_clauses": len(cnf.clauses),
           "variables": len({abs(l) for c in cnf.clauses for l in c}),
           "drat_verified": "s VERIFIED" in out.stdout, "irreducible": irreducible,
           "drat_tail": out.stdout.strip().splitlines()[-3:]}
    json.dump(rec, open(base + ".json", "w"), indent=1)
    print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), sys.argv[3])
