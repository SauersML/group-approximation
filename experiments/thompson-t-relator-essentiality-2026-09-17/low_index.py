"""Transitive permutation representations of relator-dropped Lochak--Schneps presentations.

G0 = <a, b | a^4, b^3>,  Delta = G0 / <<(ba)^5>>,
G_1 = Delta / <<r_1>>,  G_2 = Delta / <<r_2>>,  T = Delta / <<r_1, r_2>>.

For each subgroup H of index <= N in G_i (sympy low_index_subgroups), build the coset action,
evaluate the omitted relator r_j on it, and record whether r_j acts nontrivially.  A transitive
action of G_i on which r_j is nontrivial is a finite quotient of G_i in which r_j survives.

Usage: python3 low_index.py WHICH N     (WHICH in {1, 2, P, 12})
"""
import sys, time, json
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup, low_index_subgroups
from sympy.combinatorics import Permutation

F, a, b = free_group("a b")


def comm(x, y):
    return x**-1 * y**-1 * x * y


X = b * a * b
J = a**2
W = a**2 * b**2 * a**2
r1 = comm(X, J * X * J)
r2 = comm(X, W * X * W**-1)
rP = (b * a)**5
REL = {"1": r1, "2": r2, "P": rP}

which, N = sys.argv[1], int(sys.argv[2])
rels = [a**4, b**3]
for ch in which:
    rels.append(REL[ch])
G = FpGroup(F, rels)
t0 = time.time()
tables = low_index_subgroups(G, N)
out = {"which": which, "N": N, "count": len(tables), "reps": []}


def act(table, word):
    """Permutation of cosets induced by a free-group word (cosets act on the right)."""
    n = len(table.table)
    img = list(range(n))
    for sym, e in word.array_form:
        gi = table.A.index(F.generators[[str(g) for g in F.generators].index(str(sym))]**(1 if e > 0 else -1))
        for _ in range(abs(e)):
            img = [table.table[c][gi] for c in img]
    return img


for C in tables:
    C.compress(); C.standardize()
    n = len(C.table)
    res = {"index": n}
    for name, w in (("r1", r1), ("r2", r2), ("rP", rP)):
        p = act(C, w)
        res[name] = sum(1 for i in range(n) if p[i] != i)  # moved points
    pa, pb = Permutation(act(C, a)), Permutation(act(C, b))
    from sympy.combinatorics import PermutationGroup
    Gp = PermutationGroup([pa, pb])
    res["order"] = int(Gp.order())
    res["a_order"], res["b_order"] = int(pa.order()), int(pb.order())
    out["reps"].append(res)
out["seconds"] = round(time.time() - t0, 1)
print(json.dumps(out))
