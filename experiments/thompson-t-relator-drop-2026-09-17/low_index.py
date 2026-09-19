"""Low-index subgroups of the relator-dropped Lochak--Schneps groups.

G_P  = < a, b | a^4, b^3, (ba)^5 >                 (= Delta(4,3,5))
G_1  = G_P / << r_1 >>,   G_2 = G_P / << r_2 >>,   T = G_P / << r_1, r_2 >>.

r_1 = [X, J X J], r_2 = [X, W X W^-1], X = bab, J = a^2, W = a^2 b^2 a^2.
Prints the number of conjugacy classes of subgroups of index <= N for each.
T has none of index > 1, so any proper finite-index subgroup of G_1 or G_2
shows that the dropped relator is not a consequence of the others.
"""
import sys
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup, low_index_subgroups

F, a, b = free_group("a b")
X = b * a * b
J = a ** 2
W = a ** 2 * b ** 2 * a ** 2
Wi = W ** -1


def comm(u, v):
    return u * v * u ** -1 * v ** -1


r1 = comm(X, J * X * J ** -1)
r2 = comm(X, W * X * Wi)
base = [a ** 4, b ** 3, (b * a) ** 5]
groups = {"G_P": base, "G_1": base + [r1], "G_2": base + [r2], "T": base + [r1, r2]}

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
for name, rels in groups.items():
    G = FpGroup(F, rels)
    L = low_index_subgroups(G, N)
    print(name, "index<=%d classes:" % N, len(L), flush=True)
