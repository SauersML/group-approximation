"""Describe the transitive permutation quotients found by low_index.py:
for each subgroup class, the index and the order of the permutation image."""
import sys
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup, low_index_subgroups
from sympy.combinatorics import Permutation, PermutationGroup

F, a, b = free_group("a b")
X = b * a * b
J = a ** 2
W = a ** 2 * b ** 2 * a ** 2


def comm(u, v):
    return u * v * u ** -1 * v ** -1


r1 = comm(X, J * X * J ** -1)
r2 = comm(X, W * X * W ** -1)
base = [a ** 4, b ** 3, (b * a) ** 5]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 7
for name, rels in {"G_1": base + [r1], "G_2": base + [r2]}.items():
    G = FpGroup(F, rels)
    for C in low_index_subgroups(G, N, ):
        n = len(C.table)
        if n == 1:
            continue
        # columns of the coset table: a, a^-1, b, b^-1
        pa = Permutation([C.table[i][0] for i in range(n)])
        pb = Permutation([C.table[i][2] for i in range(n)])
        P = PermutationGroup([pa, pb])
        print(name, "index", n, "image order", P.order(), "perfect?", P.is_perfect,
              "orders a,b:", pa.order(), pb.order())
