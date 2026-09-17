#!/usr/bin/env python3
"""Rank-(1,3) and rank-(2,4) bowtie search in [1,c]_W, c = s_1 ... s_n, for Coxeter groups with labels in {2,3,4,5}
and nondegenerate Tits form (the label-4 groups [5,3,3,4], [4,3,5] and spherical controls B_4, F_4, B_5).

Usage: bowties_label4.py <group> <height bound H> <mode 13|24> [cap]
       env CERT_OUT=file.json writes the first candidate with det <= 0 (CONTROL=1: with none, an uncertified one).

Arithmetic.  Root coordinates live in Z[sqrt2, phi]; an element is a 4-tuple of ints (a, b, c, d) meaning
a + b phi + (c + d phi) sqrt2.  Products of reflections are exact matrices over this ring, so equal subword products
are detected exactly.  The sign of det chi_c is computed in floating point with 60 significant digits (mpmath) and is
only a filter: every certificate is re-checked in exact symbolic arithmetic by verify_bowtie_label4.py, which shares
no code with this script.

Shapes (lemma D of research/noncrossing-interval-of-5-3-3-11-is-not-a-lattice-proof.md: det chi_c|Mov(z) > 0 for
every z in [1,c]_W):
  13: reflections a != b below rank-3 p != q with det chi_c|span(alpha_a, alpha_b) <= 0 (no rank-2 element above).
  24: (n = 5) rank-2 x != y below coatoms u != v with dim(Mov x + Mov y) = 3 and det chi_c|(Mov x + Mov y) <= 0.
Relations come from subwords of reduced reflection factorizations of c in the bounded Hurwitz orbit (roots of
height <= H).  Only lower bounds on the poset are used; 0 certificates at a bound proves nothing.
"""
import sys, itertools, time, os, json
import mpmath as mp
mp.mp.dps = 60

GROUPS = {
    'B4':   (4, {(0,1):4, (1,2):3, (2,3):3}),
    'F4':   (4, {(0,1):3, (1,2):4, (2,3):3}),
    'B5':   (5, {(0,1):4, (1,2):3, (2,3):3, (3,4):3}),
    '435':  (4, {(0,1):4, (1,2):3, (2,3):5}),
    '5334': (5, {(0,1):5, (1,2):3, (2,3):3, (3,4):4}),
    # label-{2,3,5} groups, for cross-checking against rank3_bowties.py / rank24_bowties.py
    '53311': (5, {(0,1):5, (1,2):3, (2,3):3, (2,4):3}),
    '5333':  (5, {(0,1):5, (1,2):3, (2,3):3, (3,4):3}),
    '5335':  (5, {(0,1):5, (1,2):3, (2,3):3, (3,4):5}),
    '535':   (4, {(0,1):5, (1,2):3, (2,3):5}),
}
ZERO = (0, 0, 0, 0); ONE = (1, 0, 0, 0)
PHI = mp.mpf(1) / 2 + mp.sqrt(5) / 2; SQ2 = mp.sqrt(2)
def phimul(x, y):
    a, b = x; c, d = y
    return (a*c + b*d, a*d + b*c + b*d)
def rmul(x, y):
    A1, A2, B1, B2 = x[:2], x[2:], y[:2], y[2:]
    p = phimul(A1, B1); q = phimul(A2, B2); r = phimul(A1, B2); s = phimul(A2, B1)
    return (p[0] + 2*q[0], p[1] + 2*q[1], r[0] + s[0], r[1] + s[1])
def radd(x, y): return tuple(u + v for u, v in zip(x, y))
def rsub(x, y): return tuple(u - v for u, v in zip(x, y))
def rneg(x): return tuple(-u for u in x)
def rval(x): return x[0] + x[1]*PHI + (x[2] + x[3]*PHI)*SQ2
TWOB = {1: (2, 0, 0, 0), 2: ZERO, 3: (-1, 0, 0, 0), 4: (0, 0, -1, 0), 5: (0, -1, 0, 0)}

def setup(name):
    n, edges = GROUPS[name]
    T = [[TWOB[1] if i == j else ZERO for j in range(n)] for i in range(n)]
    for (i, j), m in edges.items(): T[i][j] = T[j][i] = TWOB[m]
    return n, T
def pair2B(T, x, y):
    acc = ZERO; n = len(x)
    for i in range(n):
        if x[i] == ZERO: continue
        for j in range(n):
            if y[j] == ZERO or T[i][j] == ZERO: continue
            acc = radd(acc, rmul(rmul(x[i], T[i][j]), y[j]))
    return acc
def reflect(T, beta, x):
    k = pair2B(T, x, beta)
    return tuple(rsub(x[i], rmul(k, beta[i])) for i in range(len(x)))
def normalize(r):
    for x in r:
        if x != ZERO:
            v = rval(x); assert abs(v) > mp.mpf(10) ** -30
            return r if v > 0 else tuple(rneg(y) for y in r)
    raise ValueError('zero root')
def height(r): return float(sum(abs(rval(x)) for x in r))
def refl_matrix(T, beta):
    n = len(beta)
    cols = [reflect(T, beta, tuple(ONE if i == j else ZERO for i in range(n))) for j in range(n)]
    return tuple(tuple(cols[j][i] for j in range(n)) for i in range(n))
def rm_mul(X, Y):
    n = len(X)
    return tuple(tuple(_rsum(rmul(X[i][k], Y[k][j]) for k in range(n) if X[i][k] != ZERO and Y[k][j] != ZERO)
                       for j in range(n)) for i in range(n))
def _rsum(it):
    acc = ZERO
    for x in it: acc = radd(acc, x)
    return acc
def hurwitz_orbit(n, T, H, cap):
    start = tuple(tuple(ONE if i == j else ZERO for i in range(n)) for j in range(n))
    seen = {start}; frontier = [start]
    while frontier:
        nxt = []
        for f in frontier:
            for i in range(n - 1):
                a, b = f[i], f[i+1]
                for new in ((normalize(reflect(T, a, b)), a), (b, normalize(reflect(T, b, a)))):
                    if height(new[0]) > H or height(new[1]) > H: continue
                    g = f[:i] + new + f[i+2:]
                    if g not in seen:
                        seen.add(g); nxt.append(g)
                        if len(seen) >= cap: return seen, False
        frontier = nxt
    return seen, True

def main():
    name = sys.argv[1]; H = float(sys.argv[2]); mode = sys.argv[3]; cap = int(sys.argv[4]) if len(sys.argv) > 4 else 300000
    n, T = setup(name); t0 = time.time()
    rmc = {}
    def R(beta):
        if beta not in rmc: rmc[beta] = refl_matrix(T, beta)
        return rmc[beta]
    pc = {}
    def P(letters):
        if letters not in pc:
            m = R(letters[0])
            for r in letters[1:]: m = rm_mul(m, R(r))
            pc[letters] = m
        return pc[letters]
    c = P(tuple(tuple(ONE if i == j else ZERO for i in range(n)) for j in range(n)))
    Bf = mp.matrix([[rval(T[i][j]) / 2 for j in range(n)] for i in range(n)])
    cf = mp.matrix([[rval(c[i][j]) for j in range(n)] for i in range(n)])
    chi = Bf * mp.inverse(mp.eye(n) - cf)
    facts, closed = hurwitz_orbit(n, T, H, cap)
    facts = sorted(facts)
    print(f'[{name}] n={n} H={H} mode={mode}: {len(facts)} reduced reflection factorizations of c (bounded orbit closed: {closed})')
    assert all(P(f) == c for f in facts[:500])
    vec = lambda r: mp.matrix([rval(x) for x in r])
    def gram_det(cols):
        E = mp.matrix(n, len(cols))
        for j, r in enumerate(cols):
            for i in range(n): E[i, j] = rval(r[i])
        return mp.det(E.T * chi * E)
    stats = {}; certs = []
    def bump(k): stats[k] = stats.get(k, 0) + 1
    if mode == '13':
        witness = {}; atoms_of = {}
        for f in facts:
            for S in itertools.combinations(range(n), 3):
                p = P(tuple(f[i] for i in S))
                atoms_of.setdefault(p, set()).update(f[i] for i in S)
                for i in S: witness.setdefault((p, f[i]), (f, list(S)))
        tops = {}
        for p, ats in atoms_of.items():
            for a, b in itertools.combinations(sorted(ats), 2): tops.setdefault((a, b), []).append(p)
        multi = {k: v for k, v in tops.items() if len(v) >= 2}
        print(f'  rank-3 elements: {len(atoms_of)}; atom pairs below >= 2 rank-3 elements: {len(multi)} [{time.time()-t0:.1f}s]')
        for (a, b), ps in multi.items():
            d = gram_det([a, b])
            if d > mp.mpf(10) ** -40: bump('det > 0'); continue
            bump('det <= 0 (candidate)'); certs.append((a, b, ps[0], ps[1]))
        if os.environ.get('CERT_OUT') and not certs and os.environ.get('CONTROL') and multi:
            (a, b), ps = next(iter(multi.items())); certs = [(a, b, ps[0], ps[1])]
        if os.environ.get('CERT_OUT') and certs:
            a, b, p, q = certs[0]
            out = {'shape': '13', 'alpha_a': a, 'alpha_b': b,
                   'top1_witnesses': [witness[(p, a)], witness[(p, b)]], 'top2_witnesses': [witness[(q, a)], witness[(q, b)]]}
    elif mode == '24':
        assert n == 5
        below, letters_of, witness = {}, {}, {}
        for f in facts:
            for k in range(n):
                S4 = [i for i in range(n) if i != k]
                u = P(tuple(f[i] for i in S4)); bu = below.setdefault(u, set())
                for S2 in itertools.combinations(S4, 2):
                    x = P(tuple(f[i] for i in S2)); bu.add(x); letters_of.setdefault(x, (f[S2[0]], f[S2[1]]))
                    witness.setdefault((x, u), (f, list(S2), S4))
        tops = {}
        for u, xs in below.items():
            for x, y in itertools.combinations(sorted(xs), 2): tops.setdefault((x, y), []).append(u)
        multi = {k: v for k, v in tops.items() if len(v) >= 2}
        print(f'  coatoms: {len(below)}; rank-2 pairs below >= 2 coatoms: {len(multi)} [{time.time()-t0:.1f}s]')
        for (x, y), us in multi.items():
            vs = list(letters_of[x]) + list(letters_of[y])
            M = mp.matrix([[rval(t) for t in v] for v in vs])
            sv = mp.svd_r(M, compute_uv=False)
            rk = sum(1 for s in sv if s > mp.mpf(10) ** -30)
            if rk != 3: bump(f'dim U = {rk}'); continue
            basis = []
            for v in vs:
                Mb = mp.matrix([[rval(t) for t in w] for w in basis + [v]])
                if sum(1 for s in mp.svd_r(Mb, compute_uv=False) if s > mp.mpf(10) ** -30) > len(basis): basis.append(v)
            d = gram_det(basis)
            if d > mp.mpf(10) ** -40: bump('det > 0'); continue
            bump('det <= 0 (candidate)'); certs.append((x, y, us[0], us[1]))
        if os.environ.get('CERT_OUT') and not certs and os.environ.get('CONTROL') and multi:
            (x, y), us = next(iter(multi.items())); certs = [(x, y, us[0], us[1])]
        if os.environ.get('CERT_OUT') and certs:
            x, y, u, v = certs[0]
            out = {'shape': '24', 'top1_witnesses': [witness[(x, u)], witness[(y, u)]],
                   'top2_witnesses': [witness[(x, v)], witness[(y, v)]]}
    print(f'  verdicts: {stats}')
    print(f'  CANDIDATE RANK-({mode[0]},{mode[1]}) BOWTIES (det <= 0 numerically): {len(certs)} [{time.time()-t0:.1f}s]')
    if os.environ.get('CERT_OUT') and certs:
        out.update({'group': name, 'n': n, 'edges': [[i, j, m] for (i, j), m in GROUPS[name][1].items()]})
        json.dump(out, open(os.environ['CERT_OUT'], 'w'), indent=1)
        print('  first candidate written to', os.environ['CERT_OUT'])

if __name__ == '__main__':
    main()
