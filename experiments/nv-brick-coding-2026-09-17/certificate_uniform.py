"""Complete certificate: no brick coding in any dimension for the five q = 2 examples.

Proposition B of research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md says:
given (R1) row sums 4 and primitivity, (R2) dim H^1(K; Q) = 2 and (R3) one transport
class per colour, every brick coding has dimension m <= 2 and total code length 2 on
every edge.  A dimension-1 coding padded by empty words is a dimension-2 solution of
(B1)+(B2), so it suffices that the uniform (total length 2) dimension-2 instance is UNSAT.

This script runs certificate.main(solve_sat=False) (hypotheses (R1)-(R3)) and then the
uniform m = 2 instance with two independent SAT solvers for each example.
"""
from pysat.solvers import Cadical153, Glucose4
import json
import brick_sat, certificate

if __name__ == "__main__":
    certificate.main(solve_sat=False)
    ex = json.load(open("tp_q2.json"))["examples"]
    for k, (lam, T, _) in enumerate(ex):
        T = [tuple(t) for t in T]
        for solver in (Cadical153, Glucose4):
            print(f"T{k}:", end=" ", flush=True)
            assert brick_sat.solve(T, 2, uniform=True, solver=solver) is None
    print("uniform certificate passed: no brick coding in any dimension for T0..T4")
