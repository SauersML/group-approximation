"""Pin-moment hierarchy for the Had_3 -> Max-2Lin(2) minimax R*(3).

Setting (as in research/hadamard-gadget-deletion-ratio-window.md): K = 2^k,
Q = {-1,1}^K encoded as K-bit integers (bit j set <=> x_j = -1), pins
chi_a(j) = (-1)^{a.j}, length-one edges (x, x ^ (1<<j)).  A folded adversary
f satisfies f(-x) = -f(x); its pin pattern is xi_a = f(chi_a).

For an edge weighting w (a probability vector on edges) and a pattern xi,
m_w(xi) = min over folded f with pattern xi of sum_e w_e [f cuts e]
(exact, by a 0/1 MILP: `price`), and m^U_w(xi) the same minimum over relaxed
f (f(chi_a) = xi_a, f(-chi_a) = -xi_a, unfolded elsewhere; an s-t min cut:
`uprice`).  m^U <= m.  For G-invariant w (G = affine maps of the coordinate
index set, sign flips by characters, negation), m_w is constant on the three
coset classes of patterns modulo the signed code RM(1,3):
  lin  (1/16 of patterns), quad = rank-2 quadratic cosets (7/16),
  cub  = cosets of degree 3 (8/16).

Values computed (column generation, exact pricing):
  R*(3)   = K max_w  [ m_lin/16 + 7 m_quad/16 + m_cub/2 ]          (true)
  R_t(3)  = K max_w  min( m_cub , (m_lin + 7 m_quad)/8 )  for 4 <= t <= 7
  R_3(3)  = K max_w  min( m_lin, m_quad, m_cub ) = K max_w m_lin (= 1)
R_t is the value of the relaxation in which the adversary's pin pattern need
only be t-wise uniform (see research/hadamard-certificates-blind-below-planes.md).
"""
import itertools
import sys
import numpy as np
from scipy.optimize import milp, linprog, LinearConstraint, Bounds

k = 3
K = 1 << k
FULL = (1 << K) - 1
NQ = 1 << K


def dot(a, j):
    return bin(a & j).count("1") & 1


CHI = [sum(dot(a, j) << j for j in range(K)) for a in range(K)]

# ---- edges and their orbits under G --------------------------------------
EDGES = [(x, j) for x in range(NQ) for j in range(K) if not (x >> j) & 1]
EID = {e: i for i, e in enumerate(EDGES)}
E = len(EDGES)


def norm(x, j):
    return (x & ~(1 << j), j)


def perm_point(p, x):
    y = 0
    for j in range(K):
        if (x >> j) & 1:
            y |= 1 << p[j]
    return y


def rot(j):
    return ((j << 1) | (j >> (k - 1))) & (K - 1)


COORD_PERMS = [
    [j ^ 1 for j in range(K)],                    # translation
    [rot(j) for j in range(K)],                   # cyclic linear map
    [j ^ ((j & 1) << 1) for j in range(K)],       # transvection
    [(j & ~3) | ((j & 1) << 1) | ((j >> 1) & 1) for j in range(K)],  # swap bits 0,1
]
MASKS = [CHI[1 << i] for i in range(k)] + [FULL]


def gens_edge(e):
    x, j = e
    for p in COORD_PERMS:
        yield norm(perm_point(p, x), p[j])
    for m in MASKS:
        yield norm(x ^ m, j)


parent = list(range(E))


def find(i):
    while parent[i] != i:
        parent[i] = parent[parent[i]]
        i = parent[i]
    return i


for e in EDGES:
    for f in gens_edge(e):
        a, b = find(EID[e]), find(EID[f])
        if a != b:
            parent[a] = b
ROOTS = sorted({find(i) for i in range(E)})
ORB = np.array([ROOTS.index(find(i)) for i in range(E)])
NO = len(ROOTS)
ORB_SIZE = np.bincount(ORB, minlength=NO)
EX = np.array([e[0] for e in EDGES])
EY = np.array([e[0] | (1 << e[1]) for e in EDGES])
EJ = np.array([e[1] for e in EDGES])

# ---- folded pricing by MILP ---------------------------------------------
REPS = [x for x in range(NQ) if not x & 1]           # x_0 = +1 half
RIDX = {r: i for i, r in enumerate(REPS)}
NR = len(REPS)


def rep(x):
    """(index of representative, sign) with f(x) = sign * s_rep."""
    return (RIDX[x], 0) if not x & 1 else (RIDX[x ^ FULL], 1)


EDGE_REP = [(rep(int(EX[i])), rep(int(EY[i]))) for i in range(E)]


def pattern_bits(q):
    """pin pattern xi_a = (-1)^{q(a)}; returns list of (rep index, bit) with
    bit b meaning s_rep = (-1)^b."""
    out = []
    for a in range(K):
        r, sg = rep(CHI[a])
        out.append((r, q(a) ^ sg))
    return out


def price(wedge, q):
    """exact m_w for pattern q: returns (value, per-edge cut 0/1 vector)."""
    nv = NR + E
    cost = np.concatenate([np.zeros(NR), wedge])
    A = np.zeros((2 * E, nv)); lo = np.zeros(2 * E); hi = np.full(2 * E, np.inf)
    for i, ((r1, s1), (r2, s2)) in enumerate(EDGE_REP):
        c = NR + i
        A[2 * i, c] = 1; A[2 * i + 1, c] = 1
        if s1 ^ s2 == 0:      # cut iff b1 != b2
            A[2 * i, r1] -= 1; A[2 * i, r2] += 1
            A[2 * i + 1, r1] += 1; A[2 * i + 1, r2] -= 1
        else:                 # cut iff b1 == b2
            A[2 * i, r1] += 1; A[2 * i, r2] += 1; lo[2 * i] = 1
            A[2 * i + 1, r1] -= 1; A[2 * i + 1, r2] -= 1; lo[2 * i + 1] = -1
    lb = np.zeros(nv); ub = np.ones(nv)
    for r, bit in pattern_bits(q):
        lb[r] = ub[r] = bit
    integ = np.concatenate([np.ones(NR), np.zeros(E)])
    res = milp(cost, constraints=LinearConstraint(A, lo, hi), integrality=integ,
               bounds=Bounds(lb, ub), options={"mip_rel_gap": 0, "disp": False})
    assert res.success, res.message
    b = np.round(res.x[:NR]).astype(int)
    cut = np.zeros(E, dtype=int)
    for i, ((r1, s1), (r2, s2)) in enumerate(EDGE_REP):
        cut[i] = b[r1] ^ b[r2] ^ s1 ^ s2
    return float(wedge @ cut), cut


def uprice(wedge_int, q):
    """exact relaxed (unfolded) minimum for integer edge weights: s-t min cut.
    returns (value, per-edge cut 0/1 vector, f as bool array True=+1)."""
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import maximum_flow
    s, t = NQ, NQ + 1
    big = int(wedge_int.sum()) + 1
    us, vs, cs = [], [], []
    for i in range(E):
        if wedge_int[i] > 0:
            us += [EX[i], EY[i]]; vs += [EY[i], EX[i]]; cs += [wedge_int[i]] * 2
    for a in range(K):
        v = CHI[a]
        plus = q(a) == 0                       # f(chi_a) = +1
        for node, pos in ((v, plus), (v ^ FULL, not plus)):
            if pos:
                us.append(s); vs.append(node)
            else:
                us.append(node); vs.append(t)
            cs.append(big)
    M = csr_matrix((np.array(cs, dtype=np.int32), (us, vs)), shape=(NQ + 2, NQ + 2))
    res = maximum_flow(M, s, t)
    R = (M - res.flow).tocsr()                 # residual capacities (summed duplicates)
    R.data = np.maximum(R.data, 0); R.eliminate_zeros()
    from scipy.sparse.csgraph import breadth_first_order
    reach = breadth_first_order(R, s, directed=True, return_predecessors=False)
    f = np.zeros(NQ + 2, dtype=bool); f[reach] = True
    f = f[:NQ]
    cut = (f[EX] != f[EY]).astype(int)
    val = int(wedge_int @ cut)
    assert val == res.flow_value, (val, res.flow_value)
    return val, cut, f


CLASSES = {
    "lin": lambda a: 0,
    "quad": lambda a: (a & 1) & ((a >> 1) & 1),
    "cub": lambda a: (a & 1) & ((a >> 1) & 1) & ((a >> 2) & 1),
}
PROB = {"lin": 1 / 16, "quad": 7 / 16, "cub": 8 / 16}
NAMES = list(CLASSES)


def combine(mode, v):
    """v: dict class -> value.  The objective of each relaxation."""
    if mode == "true":
        return sum(PROB[c] * v[c] for c in NAMES)
    if mode == "mom7":
        return min(v["cub"], (v["lin"] + 7 * v["quad"]) / 8)
    return min(v.values())


def solve(mode, iters=300, tol=1e-9):
    """column generation for K max_w combine(mode, m_w)."""
    pool = {c: [] for c in NAMES}
    nv = NO + 3 + 1
    U = NO + 3
    for it in range(iters):
        A_ub, b_ub = [], []
        for ci, c in enumerate(NAMES):
            for cnt in pool[c]:
                row = np.zeros(nv); row[NO + ci] = 1; row[:NO] = -cnt
                A_ub.append(row); b_ub.append(0)
        if mode == "true":
            row = np.zeros(nv); row[U] = 1
            for ci, c in enumerate(NAMES):
                row[NO + ci] = -PROB[c]
            A_ub.append(row); b_ub.append(0)
        elif mode == "mom7":
            row = np.zeros(nv); row[U] = 1; row[NO + 2] = -1
            A_ub.append(row); b_ub.append(0)
            row = np.zeros(nv); row[U] = 1; row[NO] = -1 / 8; row[NO + 1] = -7 / 8
            A_ub.append(row); b_ub.append(0)
        else:
            for ci in range(3):
                row = np.zeros(nv); row[U] = 1; row[NO + ci] = -1
                A_ub.append(row); b_ub.append(0)
        obj = np.zeros(nv); obj[U] = -1
        A_eq = np.zeros((1, nv)); A_eq[0, :NO] = ORB_SIZE
        bounds = [(0, None)] * NO + [(0, 1)] * 4
        res = linprog(obj, A_ub=np.array(A_ub), b_ub=b_ub, A_eq=A_eq, b_eq=[1],
                      bounds=bounds, method="highs")
        wo = res.x[:NO]; y = res.x[NO:NO + 3]; ub_val = -res.fun
        wedge = wo[ORB]
        m, added = {}, 0
        for ci, c in enumerate(NAMES):
            v, cut = price(wedge, CLASSES[c])
            m[c] = v
            if v < y[ci] - tol:
                pool[c].append(np.bincount(ORB, weights=cut, minlength=NO))
                added += 1
        lb_val = combine(mode, m)
        print(f"{mode} it {it}: LP ub {K*ub_val:.9f}  certified lb {K*lb_val:.9f}  K*m = "
              + ", ".join(f"{c}:{K*m[c]:.6f}" for c in NAMES), flush=True)
        if added == 0 or K * (ub_val - lb_val) < 1e-8:
            break
    return K * lb_val, K * ub_val, wo, m


if __name__ == "__main__":
    print(f"k={k}: {E} edges, {NO} edge orbits under G, sizes {list(ORB_SIZE)}")
    for mode in sys.argv[1:] or ["true", "mom7", "mom3"]:
        lb, ub, wo, m = solve(mode)
        print(f"RESULT {mode}: value in [{lb:.9f}, {ub:.9f}]  "
              f"w_orbit={np.round(wo, 7).tolist()}", flush=True)
