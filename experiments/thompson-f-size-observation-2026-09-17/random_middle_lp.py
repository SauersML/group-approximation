"""Random single-level padding: LP over mixtures of leaf-weight assignments.

Tops as in equal_middle_lp.py: complete depth-d tops on roots 0..m, INF atoms at
the two extreme leaves, every other depth-d leaf an atom of one stable level
with weight in VALUES.  A mixture p over weight assignments kills the size
observation (in this padding class) iff the law of the *direction* of the
middle weight vector (positions 1..m+d-1, normalised by its first entry) is
the same for every s in S.  This is a linear feasibility problem in p.
We minimise the total violation sum_s ||law_s - law_(s0)||_1 / 2 exactly by LP
(it is 0 iff such a mixture exists).
"""
import itertools
import sys
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

from level_search import monomial_set
from equal_middle_lp import antichain, leaves


def patterns(m, d, values):
    S = monomial_set(m, d)
    L = leaves(m, d)
    idx = {v: i for i, v in enumerate(L)}
    pieces = []
    for w in S:
        pcs = antichain(m, w)[1:-1]
        pieces.append([[idx[(b, r)] for (b, r) in L if b == a and r.startswith(q)] for (a, q) in pcs])
    assigns = list(itertools.product(values, repeat=len(L)))
    pats = []
    for asg in assigns:
        row = []
        for ps in pieces:
            ws = [sum(asg[i] for i in ids) for ids in ps]
            row.append(tuple(Fraction(x, ws[0]) for x in ws))
        pats.append(row)
    return S, assigns, pats


def solve(m, d, values):
    S, assigns, pats = patterns(m, d, values)
    na, ns = len(assigns), len(S)
    keys = sorted({p for row in pats for p in row})
    kid = {k: i for i, k in enumerate(keys)}
    nk = len(keys)
    # variables: p (na), slack u_(s,k) >= |law_s(k) - law_0(k)| for s >= 1
    nu = (ns - 1) * nk
    nvar = na + nu
    from collections import defaultdict
    ent = defaultdict(float)
    b = np.zeros(2 * nu)
    # row for (s, k, sign): sign*(law_s(k) - law_0(k)) - u_(s,k) <= 0
    for s in range(1, ns):
        for k in range(nk):
            base = 2 * ((s - 1) * nk + k)
            col_u = na + (s - 1) * nk + k
            ent[(base, col_u)] -= 1.0
            ent[(base + 1, col_u)] -= 1.0
        for j in range(na):
            ks, k0 = kid[pats[j][s]], kid[pats[j][0]]
            if ks == k0:
                continue
            for k, sg in ((ks, 1.0), (k0, -1.0)):
                base = 2 * ((s - 1) * nk + k)
                ent[(base, j)] += sg
                ent[(base + 1, j)] -= sg
    from scipy.sparse import coo_matrix
    rows_, cols_, vals_ = zip(*[(r_, c_, v_) for (r_, c_), v_ in ent.items() if v_ != 0.0])
    A = coo_matrix((vals_, (rows_, cols_)), shape=(2 * nu, nvar))
    A_eq = np.zeros((1, nvar))
    A_eq[0, :na] = 1.0
    c = np.concatenate([np.zeros(na), np.ones(nu) / 2])
    res = linprog(c, A_ub=A.tocsr(), b_ub=b, A_eq=A_eq, b_eq=[1.0],
                  bounds=[(0, None)] * nvar, method="highs")
    return res.fun, na, nk


if __name__ == "__main__":
    values = [int(x) for x in sys.argv[1].split(",")]
    cases = [tuple(int(x) for x in c.split(",")) for c in sys.argv[2:]]
    for (m, d) in cases:
        val, na, nk = solve(m, d, values)
        print(f"m={m} d={d} values={values}: assignments={na}, pattern keys={nk}, "
              f"min total violation = {val:.6g}", flush=True)
