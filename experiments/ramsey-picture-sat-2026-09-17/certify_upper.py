"""Independent certificate for rho_G(B_1, n) <= bound, from the CEGAR output cegar_{G}_n{n}.json.

Step 1 (exact).  For every certificate collection C, recompute an optimal lambda on C by LP,
rationalise it (limit_denominator), and check with Fractions that lambda is a probability
vector on C whose coverage vector v_a = sum_{P ni a} lambda_P has max - min <= bound.
Step 2 (DRAT).  Build the CNF  base  AND  blocking, where base = for every g in I_n and every
pattern P:  (pattern of E at g is P) -> r_P,  and blocking = for every C: OR_{P in C} not r_P.
Solve it once with a proof trace; write DIMACS + DRAT; check with drat-trim.
If the CNF is UNSAT then every E subset B_n realizes some C entirely (take r_P = [P realized]),
so bal(Y_E) <= bal(C) <= bound, i.e. B_n is bound-Ramsey w.r.t. B_1.
usage: python3 certify_upper.py {F|F2|Z2} n bound drat_trim_binary
"""
import json
import subprocess
import sys
from fractions import Fraction as Q

from pysat.formula import CNF
from pysat.solvers import Glucose4

from cegar import bal
from ramsey_sat import setup


def exact_check(C, k, bound):
    for den in (12, 60, 360, 2520, 10 ** 4, 10 ** 6):
        _, lam = bal(C, k)
        lq = {P: Q(x).limit_denominator(den) for P, x in lam.items()}
        lq = {P: x for P, x in lq.items() if x > 0}
        tot = sum(lq.values())
        lq = {P: x / tot for P, x in lq.items()}
        v = [sum(x for P, x in lq.items() if P >> a & 1) for a in range(k)]
        if max(v) - min(v) <= bound:
            return {str(P): str(x) for P, x in lq.items()}
    return None


def main(name, n, bound, drat):
    res = json.load(open(f"cegar_{name}_n{n}.json"))
    dist, idx, interior, k = setup(name, n)
    N = len(dist)
    assert N == res["ball"] and len(interior) == res["interior"]
    certs = [c["C"] for c in res["certificates"]]
    lam_exact = []
    for C in certs:
        lq = exact_check(C, k, bound)
        assert lq is not None, C
        lam_exact.append(lq)
    rvar = {P: N + 1 + P for P in range(1 << k)}
    cnf = CNF()
    for row in interior:
        for P in range(1 << k):
            cnf.append([(-v if P >> i & 1 else v) for i, v in enumerate(row)] + [rvar[P]])
    for C in certs:
        cnf.append([-rvar[P] for P in C])
    base = f"certify_{name}_n{n}"
    cnf.to_file(base + ".cnf")
    # CaDiCaL's pysat proof trace omits the final conflict; Glucose4's trace is complete.
    s = Glucose4(bootstrap_with=cnf.clauses, with_proof=True)
    sat = s.solve()
    assert not sat
    with open(base + ".drat", "w") as f:
        for line in s.get_proof():
            f.write(line + "\n")
        f.write("0\n")
    s.delete()
    out = subprocess.run([drat, base + ".cnf", base + ".drat", "-w"], capture_output=True,
                         text=True, timeout=3000)
    verified = "s VERIFIED" in out.stdout
    rec = {"group": name, "n": n, "bound": str(bound), "certificates": len(certs),
           "all_bounds_exact": True, "cnf_clauses": len(cnf.clauses), "unsat": not sat,
           "drat_verified": verified,
           "drat_tail": out.stdout.strip().splitlines()[-3:]}
    json.dump({**rec, "lambda_exact": [{"C": C, "lambda": l} for C, l in zip(certs, lam_exact)]},
              open(base + ".json", "w"), indent=1)
    print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), Q(sys.argv[3]), sys.argv[4])
