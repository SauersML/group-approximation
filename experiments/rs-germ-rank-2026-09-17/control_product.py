"""Control: the product 2-graph of two full 2-shifts (the groupoid G_2^2) in the same
vertex model.  Vertices (A,B) in {0,1}^2; colour-1 edges change A, keep B; colour-2 edges
keep A, change B.  Configurations are (A_i)_i x (B_j)_j = C x C.  Every periodic point
must be NON-regular for the axis lags (the lemma of
regular-rank-two-isotropy-blocks-spatial-realization-in-g2n), so the test must report
branching everywhere.
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from periodic_column_test import test  # noqa: E402

V = [(A, B) for A in (0, 1) for B in (0, 1)]
idx = {v: i for i, v in enumerate(V)}
E1 = [(idx[(A, B)], idx[(A2, B)]) for (A, B) in V for A2 in (0, 1)]
E2 = [(idx[(A, B)], idx[(A, B2)]) for (A, B) in V for B2 in (0, 1)]

for a, b in ((1, 1), (2, 1), (2, 2), (3, 3)):
    for name, (Er, Ec) in (("lag(a,0)", (E1, E2)), ("lag(0,b)", (E2, E1))):
        res, sizes = test(Er, Ec, len(V), a, b, 2)
        nreg = sum(1 for _, v in res if all(x == 0 for x in v))
        print(f"product {name} a={a} b={b}: periodic x {len(res)}, regular {nreg}")
