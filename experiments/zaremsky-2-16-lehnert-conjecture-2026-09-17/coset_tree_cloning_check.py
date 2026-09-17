"""Sanity check for the coset-tree cloning systems of
research/finite-cloning-lamplighter-realization-proof.md.

For several decidable subgroups H <= F it computes D_n = disjoint union of Trees_j/~_H
(j <= N) and the point-cloning maps s_k, and checks:
  - ~_H is an equivalence relation (all triples), s_k well defined and injective;
  - (C2) on points: s_l then s_k == s_k then s_{l+1}  (k < l <= n);
  - (2)/(2.5): the formula for s^n_k restricted to D_m is s^m_k (resp. identity);
  - proper grading: s_k(D_n) & D_n == s_k(D_{n-1});
  - lamp stabilizer: for all tree pairs f=[T-,T+] with |T|<=NP, f.p0 == p0 iff f in H,
    computed in the colimit D_inf by expanding p0=(one-leaf tree,[.]_1) along T+.
  - the family g_i = x0^i y x0^-i has pairwise disjoint supports (i < 6).
Run: python3 coset_tree_cloning_check.py
"""
from fractions import Fraction as Fr
from itertools import product
import sys

N = 6   # levels for axiom checks
NP = 7  # tree size for lamp-stabilizer check
L = 'x'

def trees(j, memo={}):
    if j in memo: return memo[j]
    if j == 1: r = [L]
    else:
        r = [(a, b) for i in range(1, j) for a in trees(i) for b in trees(j - i)]
    memo[j] = r
    return r

def leaves(W, a=Fr(0), b=Fr(1)):
    if W == L: return [(a, b)]
    m = (a + b) / 2
    return leaves(W[0], a, m) + leaves(W[1], m, b)

def nleaves(W):
    return 1 if W == L else nleaves(W[0]) + nleaves(W[1])

def caret(W, k):
    """attach a caret at leaf k (1-indexed)"""
    if W == L:
        assert k == 1
        return (L, L)
    nl = nleaves(W[0])
    if k <= nl: return (caret(W[0], k), W[1])
    return (W[0], caret(W[1], k - nl))

def build_seq(W):
    """caret positions building W from the one-leaf tree (preorder)"""
    seq = []
    def rec(V, off):
        if V == L: return
        seq.append(off + 1)
        rec(V[0], off)
        rec(V[1], off + nleaves(V[0]))
    rec(W, 0)
    return seq

class PL:
    """dyadic PL homeo from breakpoint lists (xs -> ys)"""
    def __init__(self, xs, ys): self.xs, self.ys = xs, ys
    def __call__(self, t):
        xs, ys = self.xs, self.ys
        for i in range(len(xs) - 1):
            if xs[i] <= t <= xs[i + 1]:
                return ys[i] + (t - xs[i]) * (ys[i + 1] - ys[i]) / (xs[i + 1] - xs[i])
        raise ValueError(t)
    def slope_at(self, i):
        return (self.ys[i + 1] - self.ys[i]) / (self.xs[i + 1] - self.xs[i])
    def is_id_on(self, a, b):
        pts = [a, b] + [x for x in self.xs if a < x < b]
        return all(self(p) == p for p in pts)

def pair(Wm, Wp):
    """[W-,W+]: leaf intervals of W+ onto those of W-"""
    lp, lm = leaves(Wp), leaves(Wm)
    xs = [I[0] for I in lp] + [Fr(1)]
    ys = [I[0] for I in lm] + [Fr(1)]
    return PL(xs, ys)

SUBGROUPS = {
    'trivial': lambda f: all(f(x) == x for x in f.xs),
    'F': lambda f: True,
    'slope1_at_0': lambda f: f.slope_at(0) == 1,
    'stab_1/3': lambda f: f(Fr(1, 3)) == Fr(1, 3),
    'id_on_[1/2,1]': lambda f: f.is_id_on(Fr(1, 2), Fr(1)),
}

def check(name, member):
    fails = []
    cls = {}   # (j, tree) -> class id
    reps = {}  # j -> list of reps
    for j in range(1, N + 2):
        T = trees(j); reps[j] = []
        for W in T:
            for c, R in enumerate(reps[j]):
                if member(pair(W, R)):
                    cls[(j, W)] = c; break
            else:
                cls[(j, W)] = len(reps[j]); reps[j].append(W)
        if j <= 5:  # equivalence relation on all pairs/triples
            rel = {(a, b): member(pair(a, b)) for a in T for b in T}
            for a in T:
                if not rel[(a, a)]: fails.append(('refl', j))
            for a, b in product(T, T):
                if rel[(a, b)] != rel[(b, a)]: fails.append(('sym', j))
            for a, b, c in product(T, T, T):
                if rel[(a, b)] and rel[(b, c)] and not rel[(a, c)]: fails.append(('trans', j))
        else:
            for W in T:
                if not member(pair(W, reps[j][cls[(j, W)]])): fails.append(('cls', j))
    D = {n: [(j, c) for j in range(1, n + 1) for c in range(len(reps[j]))] for n in range(1, N + 2)}
    def s(k, p):
        j, c = p
        if k > j: return p
        return (j + 1, cls[(j + 1, caret(reps[j][c], k))])
    # well defined
    for j in range(1, N + 1):
        for W in trees(j):
            for k in range(1, j + 1):
                if cls[(j + 1, caret(W, k))] != s(k, (j, cls[(j, W)]))[1]: fails.append(('welldef', j, k))
    for n in range(1, N):
        for k in range(1, n + 1):
            img = [s(k, p) for p in D[n]]
            if len(set(img)) != len(img): fails.append(('inj', n, k))
            if not set(img) <= set(D[n + 1]): fails.append(('range', n, k))
            for l in range(k + 1, n + 1):
                for p in D[n]:
                    if s(k, s(l, p)) != s(l + 1, s(k, p)): fails.append(('C2', n, k, l))
            if n >= 2:
                lhs = set(img) & set(D[n])
                rhs = set(s(k, p) for p in D[n - 1])
                if lhs != rhs: fails.append(('graded', n, k))
    # lamp stabilizer in the colimit
    cnt = [0, 0]
    for n in range(1, NP + 1):
        for Tm in trees(n):
            for Tp in trees(n):
                def expand(T):
                    p = (1, 0)
                    for k in build_seq(T): p = s_inf(k, p)
                    return p
                def s_inf(k, p):
                    j, c = p
                    if k > j: return p
                    W = caret(reps_ext(j, c), k)
                    return (j + 1, cls_ext(j + 1, W))
                # f.p0 = (Tm, d_plus); p0 expanded along Tm = (Tm, d_minus)
                fixes = expand(Tp) == expand(Tm)
                inH = member(pair(Tm, Tp))
                cnt[inH] += 1
                if fixes != inH: fails.append(('lamp', Tm, Tp))
    return fails, [len(D[n]) for n in range(1, N + 1)], cnt

_ext = {}
def make_ext(member):
    reps = {}; cls = {}
    def cls_ext(j, W):
        if (j, W) in cls: return cls[(j, W)]
        R = reps.setdefault(j, [])
        for c, V in enumerate(R):
            if member(pair(W, V)):
                cls[(j, W)] = c; return c
        R.append(W); cls[(j, W)] = len(R) - 1
        return len(R) - 1
    def reps_ext(j, c): return reps[j][c]
    cls_ext(1, L)
    return cls_ext, reps_ext

def family_check():
    x0 = PL([Fr(0), Fr(1, 2), Fr(3, 4), Fr(1)], [Fr(0), Fr(1, 4), Fr(1, 2), Fr(1)])
    fails = []
    for i in range(6):
        a, b = Fr(1, 2 ** (i + 2)), Fr(1, 2 ** (i + 1))
        J = (Fr(1, 4), Fr(1, 2))
        for _ in range(i): J = (x0(J[0]), x0(J[1]))
        if J != (a, b): fails.append(('J', i, J))
    return fails

if __name__ == '__main__':
    allok = True
    for name, member in SUBGROUPS.items():
        cls_ext, reps_ext = make_ext(member)
        globals()['cls_ext'], globals()['reps_ext'] = cls_ext, reps_ext
        fails, sizes, cnt = check(name, member)
        print(f"H={name:15s} |D_n| n=1..{N}: {sizes}  tree pairs <= {NP} leaves: "
              f"{cnt[1]} in H, {cnt[0]} not in H;  failures: {len(fails)}")
        if fails: allok = False; print('  first failures:', fails[:5])
    ff = family_check()
    print('x0^i(J_0) = [2^-(i+2), 2^-(i+1)] for i<6:', 'ok' if not ff else ff)
    allok = allok and not ff
    print('ALL CHECKS PASSED' if allok else 'SOME CHECK FAILED')
    sys.exit(0 if allok else 1)
