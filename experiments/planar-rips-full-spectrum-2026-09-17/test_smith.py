"""Unit tests for laurent_smith.py on hand-made matrices."""
import random
import flint
from laurent_smith import torsion_of_coker, factor_invariants, P


def poly(c):
    return flint.nmod_poly([x % P for x in c], P)


t = poly([0, 1])
one = poly([1])

cases = [
    # coker L^2 / <(t-2, 0), (0, 1)> = L/(t-2)
    ([{0: t - 2 * one}, {1: one}], 2, "L/(t-2)"),
    # one relation ((t-2)(t-3), t-2): coker = L (the row is primitive? no)
    ([{0: (t - 2 * one) * (t - 3 * one), 1: t - 2 * one}], 2, "free 1 + L/(t-2)"),
    # relation (t, 1) primitive -> free rank 1, no torsion
    ([{0: t, 1: one}], 2, "free 1"),
    # t-power only: (t^3) is a unit
    ([{0: t * t * t}], 1, "free 0, no torsion"),
    # two relations generating (t-1) and (t+1) diagonal after change of basis
    ([{0: t - one, 1: one}, {0: t + one, 1: one}], 2, "L/(2) = 0 over F_p? -> L/(1)?"),
]
for rows, n, note in cases:
    free, inv, res = torsion_of_coker(rows, n)
    print(note, "| free", free, "inv", [list(map(int, f.coeffs())) for f in inv])

# random check: diag(f1, f2) conjugated by random unimodular ops
random.seed(3)
f1 = (t - 5 * one) * (t - 7 * one)
f2 = t - 5 * one
rows = [{0: f1}, {1: f2}, {2: one * 0 + one}]
# scramble rows: row0 += (t+1) row1, row2 += 3 row0
r0 = {0: f1, 1: f2 * (t + one)}
r1 = {1: f2}
r2 = {0: 3 * f1, 1: 3 * f2 * (t + one), 2: one}
free, inv, res = torsion_of_coker([r0, r1, r2], 4)
print("expect free 1, torsion (t-5)^2 (t-7):", free, factor_invariants(inv))
