"""Geodesic LP with hand-offs, for Had_k -> Max-2Lin(2) adversaries.

Take two signed primaries y0 = s0 chi_a and y1 = s1 chi_b with b != a, so
d(y0, y1) = K/2.  Let D be the set where they differ and A0 the set where
they agree (|A0| = |D| = K/2).  A geodesic from y0 to y1 flips the
coordinates of D one at a time: x_d has flip set S_d, |S_d| = d, for
d = 0 .. K/2.

Adversary class H(delta = 1/2): (i, tau) uniform and independent of xi,
and along the geodesic A(x_d) = L_d(x_d), where L_d is a random label in
  {C0, -C0, C1, -C1, D, -D},  C0 = s0 xi_a,  C1 = s1 xi_b,  D = tau x_i.
L is a Markov chain in d whose law may depend on the branch (e0, e1),
where e0 = tau-relative sign of xi_a and e1 likewise.  End conditions:
A(y0) = C0 and A(y1) = C1.

Relative to tau, put y0_i = 1.  Then D(x) = -1 if i in S else 1,
C0 = e0, and C1 = e1 * (-1 if i in D else 1).  Here e0 and e1 are
independent uniform signs, independent of i.

LP: minimize R subject to (1/4) sum_branches K Pr[cut edge d] <= R for
every d.  The flag --single forbids C0/C1 labels on the wrong half; it is
only a relaxation of the single-owner class (the midpoint is not forced to
D and the path is one geodesic, not a level average), so its values
(1.625 .. 1.734 for K = 8 .. 64) are below the class value 5/2 - 2/K.
Without the flag (hand-offs allowed) the value is 1 for K = 8 .. 128.
"""
import sys
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

LAB = ["C0", "-C0", "C1", "-C1", "D", "-D"]


def val(lab, e0, e1, loc, inS):
    # loc in {"A0", "D"}; inS: i in S (only possible if loc == "D")
    dv = -1 if inS else 1
    c0 = e0
    c1 = e1 * (-1 if loc == "D" else 1)
    base = {"C0": c0, "C1": c1, "D": dv}[lab.lstrip("-")]
    return -base if lab.startswith("-") else base


def cut(s, t, e0, e1, d, K):
    h = K // 2
    tot = 0
    # (loc, inS(x), inS(y), weight): i in A0; i in S_d; i = j; i in D minus S_{d+1}
    for loc, ix, iy, w in (("A0", False, False, h), ("D", True, True, d),
                           ("D", False, True, 1), ("D", False, False, h - d - 1)):
        if w and val(s, e0, e1, loc, ix) != val(t, e0, e1, loc, iy):
            tot += w
    return tot / K


def ok_end(lab, e0, e1, end, K):
    # label must equal C0 at y0 (S empty) / C1 at y1 (S = D) for every i
    for loc in ("A0", "D"):
        inS = (end == 1 and loc == "D")
        target = "C0" if end == 0 else "C1"
        if val(lab, e0, e1, loc, inS) != val(target, e0, e1, loc, inS):
            return False
    return True


def solve(K, single=False):
    h = K // 2
    nl = len(LAB)
    br = list(itertools.product([1, -1], [1, -1]))
    nb = len(br)
    idx = lambda b, d, s, t: ((b * h + d) * nl + s) * nl + t
    nv = nb * h * nl * nl + 1
    Ri = nv - 1
    c = np.zeros(nv); c[Ri] = 1
    Aub = lil_matrix((h, nv))
    for d in range(h):
        for b, (e0, e1) in enumerate(br):
            for s in range(nl):
                for t in range(nl):
                    Aub[d, idx(b, d, s, t)] = K * cut(LAB[s], LAB[t], e0, e1, d, K) / nb
        Aub[d, Ri] = -1
    rows = []; beq = []
    Aeq = lil_matrix((nb * (h * nl * nl + h * nl + 3 * nl + 2), nv))
    r = 0
    for b, (e0, e1) in enumerate(br):
        for s in range(nl):
            for t in range(nl):
                Aeq[r, idx(b, 0, s, t)] = 1
        beq.append(1); r += 1
        for s in range(nl):
            if not ok_end(LAB[s], e0, e1, 0, K):
                for t in range(nl):
                    Aeq[r, idx(b, 0, s, t)] = 1
                beq.append(0); r += 1
        for d in range(1, h):
            for t in range(nl):
                for s in range(nl):
                    Aeq[r, idx(b, d - 1, s, t)] += 1
                for u in range(nl):
                    Aeq[r, idx(b, d, t, u)] -= 1
                beq.append(0); r += 1
        for t in range(nl):
            if not ok_end(LAB[t], e0, e1, 1, K):
                for s in range(nl):
                    Aeq[r, idx(b, h - 1, s, t)] = 1
                beq.append(0); r += 1
        if single:
            # C1 labels only at d >= K/4 + 1 side, C0 labels only at d <= K/4 - 1
            for d in range(h):
                for s in range(nl):
                    for t in range(nl):
                        bad = False
                        for pos, lab in ((d, LAB[s]), (d + 1, LAB[t])):
                            if lab.endswith("C0") and pos >= K // 4:
                                bad = True
                            if lab.endswith("C1") and pos <= K // 4:
                                bad = True
                        if bad:
                            Aeq[r, idx(b, d, s, t)] = 1
                            beq.append(0); r += 1
    Aeq = Aeq[:r]
    res = linprog(c, A_ub=Aub.tocsr(), b_ub=np.zeros(h), A_eq=Aeq.tocsr(),
                  b_eq=np.array(beq, float), bounds=[(0, None)] * nv, method="highs")
    return res


if __name__ == "__main__":
    single = "--single" in sys.argv
    Ks = [int(a) for a in sys.argv[1:] if a.isdigit()] or [8, 16, 32, 64, 128]
    for K in Ks:
        res = solve(K, single)
        print(K, "single" if single else "handoff", res.status, res.fun)
