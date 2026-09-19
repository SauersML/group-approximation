#!/usr/bin/env python3
"""Top-level sZ of the Magnus splitting G = B_0 *_psi of G = <a,t | w>, including the
exceptional (Collins non-cyclic) case, by Stallings computations in free groups.

Setting.  B_0 = <a_0..a_n | W_0>, A = F(a_0..a_(n-1)), B = F(a_1..a_n), psi(a_i) = a_(i+1).
Linton (arXiv:2202.11324, p. 23): A_0 = {[B_0]}, A_(k+1) = {[psi(A cap C^h)] : [C] in A_k, h in B_0},
sZ(psi) = sup{k+1 : A_k has a non-cyclic class}.  A_1 = {[B]}.

Reduction (Collins, G&T Monographs 14 (2008), Thm 2).  For g in B_0, gBg^-1 cap A is cyclic unless
g in AB, and for g = ab it equals a(B cap A)a^-1.  So for any C <= B, gCg^-1 cap A is cyclic or
A-conjugate to bCb^-1 cap D with b in B, D = A cap B.  Cyclic classes only have cyclic descendants.
Hence the non-cyclic part of A_(k+1) (k >= 1) is {psi(bCb^-1 cap D) : b in B}, a computation inside
the FREE group B with the partial map phi = psi|D : D -> B.  That is exactly the forward iteration
of lintongraph.certify on K = B with A' = D (B-coordinates) and B' = psi(D) (A-coordinates shifted),
whose depth-j states are A_(j+1).  So sZ(psi) = f' + 1 where (f', b') = certify(...)['sZ'].
Symmetrically sZ(psi^-1) = f'' + 1 with certify on K = A, A'' = D (A-coordinates),
B'' = psi^-1(D) (B-coordinates shifted down).  Local coordinates: in A, a_i -> i+1; in B, a_i -> i;
then psi is the identity on local letter ids.

Computing D.  If D = F(a_1..a_(n-1)) (non-exceptional) we use it directly.  Otherwise we take the
generators of Y cap <u_h0> from magint.decide (free group V of the Magnus rewriting of W_0 along an
extreme letter s of exponent 0), express each in the Y-generators u_h = s^h u s^-h and in the
N-generators s^h0 u s^-h0, verify in V that both expressions agree, and conjugate by s^-h0.
Output: TOP w n=.. D=... rank=.. sZ(psi)=.. sZ(psi^-1)=.. (with the certify verdicts).
Calibration mode: topsz.py calib.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
for p in ('../one-relator-top-magnus-intersection-2026-09-18', '../one-relator-basis-search-2026-09-18',
          '../../research/artifacts/or-unpeelable-census-scripts-2026-09-12',
          '../../research/artifacts/one-relator-linton-graph-certificates-scripts'):
    sys.path.insert(0, os.path.normpath(os.path.join(HERE, p)))
import magint as MI
LG, fr = MI.LG, MI.fr
red, inv = LG.red, LG.inv


def expand(expr, table):
    """expr: word in generator indices (1-based, signed); table: list of words."""
    out = []
    for i in expr:
        out.extend(table[i - 1] if i > 0 else inv(table[-i - 1]))
    return red(out)


def D_from_decide(n, W0, s, Mlet, Nlet):
    """Return (status, D_M, D_N, h0) with D given as words in the B_0 letters 1..n+1 over
    the M-letters and the N-letters, or a failure status."""
    R = MI.rewrite_raw(W0, s)
    if R is None:
        return 'S-EXP-NONZERO', None, None, None
    lets = sorted(set(u for u, _, _ in R))
    rng = {u: (min(h for v, h, _ in R if v == u), max(h for v, h, _ in R if v == u)) for u in lets}
    if any(u not in rng for u in (Mlet | Nlet) - {s}):
        return 'LETTER-ABSENT', None, None, None
    gens = [(u, i) for u in lets for i in range(rng[u][0], rng[u][1] + 1)]
    idx = {g: k + 1 for k, g in enumerate(gens)}
    r = len(gens)
    m, img = MI.whmin_track([idx[(u, h)] * e for u, h, e in R], r)
    if len(m) != 1:
        return 'VERTEX-NONFREE', None, None, None
    c = abs(m[0])
    rel = {o: k + 1 for k, o in enumerate(g for g in range(1, r + 1) if g != c)}
    im = {g: tuple(fr([(rel[abs(x)] if x > 0 else -rel[abs(x)]) for x in img[idx[g]] if abs(x) != c]))
          for g in gens}
    Mp = sorted(Mlet - {s})
    Ylab = [(u, i) for u in Mp for i in range(rng[u][0], rng[u][1] + 1) if im[(u, i)]]
    Y = [im[g] for g in Ylab]
    Yp = [im[(u, i)] for u in Mp for i in range(rng[u][0] + 1, rng[u][1] + 1)]
    Ym = [im[(u, i)] for u in Mp for i in range(rng[u][0], rng[u][1])]
    Ep = [im[(u, i)] for u in lets for i in range(rng[u][0] + 1, rng[u][1] + 1)]
    Em = [im[(u, i)] for u in lets for i in range(rng[u][0], rng[u][1])]
    if not MI.sub_eq(MI.meet(Y, Ep), [g for g in Yp if g]):
        return 'NO-IMMERSION(+)', None, None, None
    if not MI.sub_eq(MI.meet(Y, Em), [g for g in Ym if g]):
        return 'NO-IMMERSION(-)', None, None, None
    lo = max(rng[u][0] for u in Nlet)
    hi = min(rng[u][1] for u in Nlet)
    if lo > hi:
        return 'N-SPLIT', None, None, None
    h0 = lo
    Nlab = [(u, h0) for u in sorted(Nlet) if im[(u, h0)]]
    Ng = [im[g] for g in Nlab]
    I = MI.meet(Y, Ng)
    if I is None:
        return 'TRIVIAL', [], [], h0
    GY, GN = TGraph(Y, True), TGraph(Ng, True)
    # I's Stallings graph: a basis of Y cap <Ng> = its base-component generators
    basis = I_basis(I)
    assert len(basis) == I.rank()
    DM, DN = [], []
    for x in basis:
        ey, en = GY.express(x), GN.express(x)
        # Y-generator (u,h) -> s^h u s^-h ; N-generator (u,h0) -> u (after conjugating by s^-h0)
        wy = []
        for i in ey:
            u, h = Ylab[abs(i) - 1]
            piece = [s] * (h - h0) if h >= h0 else [-s] * (h0 - h)
            core = piece + [u] + list(inv(piece))
            wy.extend(core if i > 0 else list(inv(core)))
        wn = []
        for i in en:
            u, _ = Nlab[abs(i) - 1]
            wn.append(u if i > 0 else -u)
        # consistency: s^h0 (wy) s^-h0 and s^h0 (wn) s^-h0 map to the same element x of V
        for w_ in (wy, wn):
            ww = [s] * h0 + list(w_) + [-s] * h0 if h0 >= 0 else [-s] * (-h0) + list(w_) + [s] * (-h0)
            Rr = MI.rewrite_raw(ww, s)
            val = red([y for (u, h, e) in Rr for y in (im[(u, h)] if e > 0 else inv(im[(u, h)]))])
            assert val == red(x), 'consistency check failed'
        DM.append(red(wy)); DN.append(red(wn))
    return 'OK', DM, DN, h0


def I_basis(Gr):
    """free basis of the subgroup with Stallings graph Gr (spanning-tree complement)."""
    out = []
    for e in Gr.E:
        g = red(Gr.tw[e[0]] + (e[1],) + inv(Gr.tw[e[2]]))
        if g and g not in out and inv(g) not in out:
            out.append(g)
    return out


class TGraph(LG.Graph):
    """Tracked Stallings graph that tolerates non-free generating sets: a type II fold just
    drops the parallel edge.  Every kept edge label still maps to the path it labels, so
    express() returns a valid (not unique) word in the given generators."""
    def _fold(self, E):
        mul = LG.mul
        while True:
            seen, hit = {}, None
            for idx, e in enumerate(E):
                for key in ((e[0], e[1], 'o'), (e[2], e[1], 'i')):
                    if key in seen: hit = (seen[key], idx, key[2]); break
                    seen[key] = idx
                if hit: break
            if not hit: return E
            i1, i2, kind = hit
            e1, e2 = E[i1], E[i2]
            if e1[0] == e2[0] and e1[2] == e2[2]:
                del E[i2]; continue
            if kind == 'o':
                if e2[2] == 0: e1, e2 = e2, e1
                x, y, s = e2[2], e1[2], mul(inv(e2[3]), e1[3])
            else:
                if e2[0] == 0: e1, e2 = e2, e1
                x, y, s = e2[0], e1[0], mul(e2[3], inv(e1[3]))
            if self.track and s:
                for e in E:
                    if e[0] == x and e[2] == x: e[3] = mul(inv(s), e[3], s)
                    elif e[0] == x: e[3] = mul(inv(s), e[3])
                    elif e[2] == x: e[3] = mul(e[3], s)
            for e in E:
                if e[0] == x: e[0] = y
                if e[2] == x: e[2] = y


def top_sz(n, W0):
    S = set(range(1, n + 1))
    T = set(range(2, n + 2))
    exps = {u: sum(1 if c == u else -1 if c == -u else 0 for c in W0) for u in range(1, n + 2)}
    tried = []
    for s, Ml, Nl in ((1, S, T), (n + 1, T, S)):
        if exps[s] != 0:
            tried.append('s=a%d:S-EXP-NONZERO' % (s - 1))
            continue
        st, DM, DN, h0 = D_from_decide(n, W0, s, Ml, Nl)
        tried.append('s=a%d:%s' % (s - 1, st))
        if st != 'OK':
            continue
        DA, DB = (DM, DN) if s == 1 else (DN, DM)
        return finish(n, DA, DB, 's=a%d h0=%d' % (s - 1, h0))
    return None, ' '.join(tried)


def finish(n, DA, DB, tag):
    Aloc = [tuple(x for x in w) for w in DA]                       # a_i -> i+1 (letter ids unchanged)
    Bloc = [tuple((abs(x) - 1) * (1 if x > 0 else -1) for x in w) for w in DB]  # a_i -> i
    rk = len(DA)
    if rk <= 1:
        return (2, 2, rk, 'cyclic', 'cyclic'), tag
    vf, inf_f = LG.certify(n, Bloc, Aloc, dmax=14)   # K = B, A' = D, B' = psi(D)
    vb, inf_b = LG.certify(n, Aloc, Bloc, dmax=14)   # K = A, A'' = D, B'' = psi^-1(D)
    szf = inf_f.get('sZ'); szb = inf_b.get('sZ')
    top_f = szf[0] + 1 if szf else None
    top_b = szb[0] + 1 if szb else None
    return (top_f, top_b, rk, '%s sZ=%s' % (vf, szf), '%s sZ=%s' % (vb, szb)), tag


def wname(w):
    return '.'.join(('a%d' % (z - 1)) if z > 0 else ('A%d' % (-z - 1)) for z in w)


def calib():
    # (1) non-exceptional n = 2: D = <a_1>, expect sZ = (2, 2)
    # (2) W_0 = [a_0,a_1][a_2,a_1]: D = <a_1, [a_0,a_1]> exceptional (= <a_1,[a_1,a_2]> in B)
    # (3) n = 3 non-exceptional D = F(a_1,a_2) computed directly and through decide
    cases = [(2, [1, 2, -1, -2, 3, 2, -3, -2])]
    for n, W0 in cases:
        res, tag = top_sz(n, W0)
        print('CALIB W0=%s -> %s %s' % (wname(W0), res, tag))
    # direct: exceptional D written by hand, check agreement with the decide-derived one
    DA = [(2,), (1, 2, -1, -2)]; DB = [(2,), (2, 3, -2, -3)]
    print('CALIB hand D for [a0,a1][a2,a1]:', finish(2, DA, DB, 'hand'))
    # non-exceptional D = F(a_1..a_(n-1)) for n = 2, 3, 4
    for n in (2, 3, 4):
        D = [(i,) for i in range(2, n + 1)]
        print('CALIB nonexc n=%d:' % n, finish(n, D, D, 'F(S cap T)'))


if __name__ == '__main__':
    if sys.argv[1] == 'calib':
        calib()
    else:
        for line in open(sys.argv[1]):
            f = line.split()
            if not f or f[0] in ('SENTINEL_DONE',):
                continue
            w = [MI.CH[c] for c in f[0]]
            n, W0 = MI.magnus(w, 2)
            res, tag = top_sz(n, W0)
            print('TOP %s n=%d W0=%s %s -> %s' % (f[0], n, wname(W0), tag, res), flush=True)
        print('SENTINEL_DONE')
