"""Scan translated subtori of the zero-sum torus {prod t = 1} of P_n:
    T(A, zeta) = { t : prod_{pairs in A} t = zeta, prod_{all pairs} t = 1 },
at random points, for twist sets A (pairs, triples, ...) and roots of unity zeta.
Reports dim H^i(P_n; L_t) for i = 0..n-1 at `samples` random points of each torus.
A positive dim H^i at every random point of a torus means V^i contains it
(up to the probability ~ (deg)/P of a spurious rank drop per sample)."""
import random, sys, json, itertools
from salvetti_jump import Setup, P, pairs, generic_on, root_of_unity

n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
samples = int(sys.argv[2]) if len(sys.argv) > 2 else 2
random.seed(20260917)
S = Setup(n)
tests = []
twist_sets = [tuple(range(k)) for k in range(2, n)]  # up to S_{n+1}: pairs, triples,...
for A in twist_sets:
    for order in (1, 2, 3, 4, 5, 6):
        tests.append(([(A, order)], f"t_{A}=zeta_{order}"))
if n >= 4:
    for o1, o2 in itertools.product((1, 2, 3), repeat=2):
        tests.append(([((0, 1), o1), ((2, 3), o2)], f"t_01=z{o1},t_23=z{o2}"))
if n >= 5:
    for o1, o2 in itertools.product((1, 2, 3), repeat=2):
        tests.append(([((0, 1), o1), ((0, 1, 2), o2)], f"t_01=z{o1},t_012=z{o2}"))
        tests.append(([((0, 1), o1), ((2, 3, 4), o2)], f"t_01=z{o1},t_234=z{o2}"))
results = []
for cons, label in tests:
    rows = []
    for _ in range(samples):
        fixed = [(A, root_of_unity(o)) for (A, o) in cons]
        t = generic_on(n, fixed)
        rows.append(S.homology(t))
    results.append({"torus": label, "dims": rows})
    print(label, rows, flush=True)
json.dump({"n": n, "P": P, "results": results},
          open(f"scan_tori_n{n}.json", "w"), indent=1)
