#!/usr/bin/env python3
"""Symbolic crossed-product engine for the Promislow group P (pure python, exact).

P = <a,b | b^-1 a^2 b = a^-2, a^-1 b^2 a = b^-2>, Gardam's affine model
(arXiv:2312.05240, proof of Thm A):
  a: v -> diag(1,-1,-1) v + (1,1,0),   b: v -> diag(-1,1,-1) v + (0,1,1).
x = a^2 = transl(2,0,0), y = b^2 = transl(0,2,0), z = (ab)^2 = transl(0,0,-2).
An element of K[P] is p + q a + r b + s ab, p,q,r,s in K[x^+-1,y^+-1,z^+-1],
coefficients on the LEFT (Gardam/Murray/Tabei convention).

Coefficient ring: Z[x^{+-1/2}, y^{+-1/2}, z^{+-1/2}][symbols]; exponents are
stored DOUBLED.  Symbols f_g (g in K4) with sigma_h(f_g) = f_{hg}; a symbol
declared ab-invariant (Gardam's p0..s0, or any function of z alone) is
canonicalized with f_C = f_e and f_B = f_A.
"""
import itertools, sys, json
from collections import defaultdict

K4 = ['e', 'A', 'B', 'C']   # e=diag(1,1,1) A=diag(1,-1,-1)=s_a B=diag(-1,1,-1)=s_b C=diag(-1,-1,1)=s_ab
SIGN = {'e': (1, 1, 1), 'A': (1, -1, -1), 'B': (-1, 1, -1), 'C': (-1, -1, 1)}
def k4mul(g, h):
    s = tuple(SIGN[g][i] * SIGN[h][i] for i in range(3))
    return next(k for k, v in SIGN.items() if v == s)

# ---------- affine model ----------
def amul(g, h):
    (s, t), (s2, t2) = g, h
    return (tuple(s[i] * s2[i] for i in range(3)), tuple(t[i] + s[i] * t2[i] for i in range(3)))
def ainv(g):
    s, t = g
    return (s, tuple(-s[i] * t[i] for i in range(3)))
E = ((1, 1, 1), (0, 0, 0))
a = ((1, -1, -1), (1, 1, 0))
b = ((-1, 1, -1), (0, 1, 1))
ab = amul(a, b)
REP = {'e': E, 'A': a, 'B': b, 'C': ab}
def aword(*gs):
    r = E
    for g in gs:
        r = amul(r, g)
    return r
assert aword(ainv(b), a, a, b, a, a) == E
assert aword(ainv(a), b, b, a, b, b) == E
assert aword(a, a) == (E[0], (2, 0, 0)) and aword(b, b) == (E[0], (0, 2, 0)) and aword(a, b, a, b) == (E[0], (0, 0, -2))

def lat_exp2(t):
    """translation vector -> DOUBLED exponent of x^i y^j z^k"""
    assert all(v % 2 == 0 for v in t), t
    return (t[0], t[1], -t[2])
def decompose(g):
    s, t = g
    c = next(k for k, v in SIGN.items() if v == s)
    tau = tuple(t[i] - REP[c][1][i] for i in range(3))
    assert amul((E[0], tau), REP[c]) == g
    return lat_exp2(tau), c
COC = {}
for c in K4:
    for d in K4:
        m, cd = decompose(amul(REP[c], REP[d]))
        assert cd == k4mul(c, d)
        COC[(c, d)] = m
def act_exp(c, m):
    s = SIGN[c]
    return (s[0] * m[0], s[1] * m[1], s[2] * m[2])
for c in K4:
    for m in [(2, 0, 0), (0, 2, 0), (0, 0, 2)]:
        tr = (E[0], (m[0], m[1], -m[2]))
        g = aword(REP[c], tr, ainv(REP[c]))
        assert g[0] == E[0] and lat_exp2(g[1]) == act_exp(c, m)

# ---------- commutative symbolic ring ----------
ABINV = set()        # names of ab-invariant symbols
def canon(name, g):
    if name in ABINV:
        return (name, 'e' if g in ('e', 'C') else 'A')
    return (name, g)
def padd(*ps):
    out = defaultdict(int)
    for p in ps:
        for k, v in p.items():
            out[k] += v
    return {k: v for k, v in out.items() if v}
def pscale(p, c):
    return {k: v * c for k, v in p.items() if v * c}
def pmul(p, q):
    out = defaultdict(int)
    for (m1, s1), v1 in p.items():
        for (m2, s2), v2 in q.items():
            out[((m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2]), tuple(sorted(s1 + s2)))] += v1 * v2
    return {k: v for k, v in out.items() if v}
def mono2(i2, j2, k2, c=1):
    return {((i2, j2, k2), ()): c}
def mono(i, j, k, c=1):
    return mono2(2 * i, 2 * j, 2 * k, c)
def sym(name, g='e'):
    return {((0, 0, 0), (canon(name, g),)): 1}
ONE = mono(0, 0, 0)
def psigma(c, p):
    out = defaultdict(int)
    for (m, s), v in p.items():
        out[(act_exp(c, m), tuple(sorted(canon(nm, k4mul(c, g)) for nm, g in s)))] += v
    return {k: v for k, v in out.items() if v}
def pmod(p, n):
    return {k: v % n for k, v in p.items() if v % n}
def poly(terms):
    """terms: list of (coef, i, j, k) with integer exponents"""
    return padd(*[mono(i, j, k, c) for c, i, j, k in terms])

# ---------- crossed product ----------
def cadd(*us):
    out = {}
    for u in us:
        for c, p in u.items():
            out[c] = padd(out.get(c, {}), p)
    return {c: p for c, p in out.items() if p}
def cscale(u, c):
    return {k: pscale(p, c) for k, p in u.items() if pscale(p, c)}
def cmul(u, v):
    out = {}
    for c, F in u.items():
        for d, G in v.items():
            term = pmul(pmul(F, psigma(c, G)), {(COC[(c, d)], ()): 1})
            cd = k4mul(c, d)
            out[cd] = padd(out.get(cd, {}), term)
    return {c: p for c, p in out.items() if p}
def elem(p=None, q=None, r=None, s=None):
    return {c: f for c, f in zip(K4, (p, q, r, s)) if f}
def cmod(u, n):
    return {c: pmod(p, n) for c, p in u.items() if pmod(p, n)}
CONE = {'e': ONE}

def rmatrix(u):
    """matrix of w -> w*u on the left module basis REP[e..C]; entry (row c, col cd)"""
    M = {(c, d): {} for c in K4 for d in K4}
    for c in K4:
        for d, F in u.items():
            cd = k4mul(c, d)
            M[(c, cd)] = padd(M[(c, cd)], pmul(psigma(c, F), {(COC[(c, d)], ()): 1}))
    return M
def det4(M):
    tot = {}
    for perm in itertools.permutations(range(4)):
        sgn = 1
        for i in range(4):
            for j in range(i + 1, 4):
                if perm[i] > perm[j]:
                    sgn = -sgn
        t = ONE
        for i in range(4):
            t = pmul(t, M[(K4[i], K4[perm[i]])])
            if not t:
                break
        if t:
            tot = padd(tot, pscale(t, sgn))
    return tot

def pstr(p, maxterms=80):
    def ms(m):
        out = []
        for v, e in zip('xyz', m):
            if e == 0:
                continue
            ee = f'{e // 2}' if e % 2 == 0 else f'({e}/2)'
            out.append(v if ee == '1' else f'{v}^{ee}')
        return '*'.join(out)
    items = sorted(p.items(), key=lambda kv: (kv[0][1], kv[0][0]))
    out = []
    for (m, s), v in items[:maxterms]:
        mon = '*'.join([f'{nm}{"" if g == "e" else "^" + g}' for nm, g in s] + ([ms(m)] if ms(m) else []))
        out.append(f'{v:+d}' + ('*' + mon if mon else ''))
    if len(items) > maxterms:
        out.append(f'... ({len(items)} terms)')
    return ' '.join(out) if out else '0'

def is_const_monomial_unit(D, modn=None):
    DD = pmod(D, modn) if modn else D
    return len(DD) == 1 and list(DD.keys())[0][1] == () and abs(list(DD.values())[0]) in ((1,) if not modn else (1,))

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'all'
    print('cocycle REP[c]REP[d] = x^(m/2) REP[cd]  (doubled exponents):')
    for c in K4:
        print('  ', c, [(d, COC[(c, d)]) for d in K4])

    # ---- validation 1: Tabei orbit-1 representative over F_2 ----
    P = pmul(pmul(poly([(1, 0, 0, 0), (1, -1, 0, 0)]), poly([(1, 0, 0, 0), (1, 0, -1, 0)])), poly([(1, 0, 0, 0), (1, 0, 0, 1)]))
    Q = poly([(1, -2, 0, 0), (1, -1, -1, -1), (1, -1, 0, -1), (1, 0, -1, 0)])
    R = poly([(1, -1, -1, 1), (1, -1, 0, 0), (1, 0, -2, 0), (1, 0, -1, 1)])
    S = poly([(1, -2, 0, 0), (1, -1, -1, 0), (1, -1, 0, -1), (1, -1, 1, 0), (1, 0, 0, 0)])
    Pp = pmul(pmul(poly([(1, 0, 0, 0), (1, 1, 0, 0)]), poly([(1, 0, 0, 0), (1, 0, 1, 0)])), poly([(1, 0, 0, 0), (1, 0, 0, -1)]))
    Qp = poly([(1, -1, 0, 0), (1, 0, -1, -1), (1, 0, 0, -1), (1, 1, -1, 0)])
    Rp = poly([(1, -1, 0, 1), (1, -1, 1, 0), (1, 0, -1, 0), (1, 0, 0, 1)])
    Sp = poly([(1, -2, 0, -1), (1, -1, -1, -1), (1, -1, 0, 0), (1, -1, 1, -1), (1, 0, 0, -1)])
    u1, u1i = elem(P, Q, R, S), elem(Pp, Qp, Rp, Sp)
    print('V1 Tabei orbit-1: u*u^-1 = 1 mod 2:', cmod(cmul(u1, u1i), 2) == CONE,
          ' u^-1*u = 1 mod 2:', cmod(cmul(u1i, u1), 2) == CONE)
    D1 = det4(rmatrix(u1))
    print('V1 det R_u mod 2:', pstr(pmod(D1, 2)))

    # ---- validation 2: Gardam 2021 Theorem A unit over F_2 via Lemma 1 ----
    def h(i2, j2, k2, c=1):
        return mono2(i2, j2, k2, c)
    vbar = padd(h(1, 0, 0), h(-1, 0, 0))
    wbar = padd(h(0, 1, 0), h(0, -1, 0))
    p0 = pmul(pmul(vbar, wbar), padd(ONE, mono(0, 0, -1)))
    gam = padd(h(-2, -1, 0), h(2, 1, 0))
    dlt = padd(h(-1, -2, 0), h(1, 2, 0))
    q0 = padd(gam, pmul(wbar, mono(0, 0, 1)))
    r0 = padd(vbar, pmul(dlt, mono(0, 0, 1)))
    s0 = padd(ONE, pmul(padd(h(-2, 0, 0), h(2, 0, 0), h(0, -2, 0), h(0, 2, 0)), mono(0, 0, -1)))
    def lemma1(p0, q0, r0, s0, sign=-1):
        p = pmul(h(1, 1, 0), p0)
        q = pmul(h(0, -1, 0), q0)
        r = pmul(h(1, 0, 0), r0)
        s = s0
        al = elem(p, q, r, s)
        alp = elem(pmul(mono(-1, 0, 0), psigma('A', p)), pscale(pmul(mono(-1, 0, 0), q), sign),
                   pscale(pmul(mono(0, -1, 0), r), sign), pmul(mono(0, 0, -1), psigma('A', s)))
        return al, alp
    for f in (p0, q0, r0, s0):
        assert psigma('C', f) == f
    al, alp = lemma1(p0, q0, r0, s0)
    print('V2 Gardam 2021 unit: all coefficients integral exponents:',
          all(m[0] % 2 == 0 and m[1] % 2 == 0 and m[2] % 2 == 0 for u in (al, alp) for p in u.values() for (m, s) in p))
    print('V2 alpha*alpha\' = 1 mod 2:', cmod(cmul(al, alp), 2) == CONE, ' alpha\'*alpha = 1 mod 2:', cmod(cmul(alp, al), 2) == CONE)
    print('V2 |supp alpha| =', sum(len(p) for p in al.values()))

    # ---- generic reduced norm ----
    p, q, r, s = sym('p'), sym('q'), sym('r'), sym('s')
    D = det4(rmatrix(elem(p, q, r, s)))
    for c in K4:
        assert psigma(c, D) == D
    print('G1 generic det R_u: terms', len(D), ' K4-invariant: True')
    print('G1 det R_u =', pstr(D, 200))

    # ---- generic Lemma-1 symmetric pieces ----
    for nm in ('P0', 'Q0', 'R0', 'S0'):
        ABINV.add(nm)
    al, alp = lemma1(sym('P0'), sym('Q0'), sym('R0'), sym('S0'))
    prod = cmul(alp, al)
    for c in K4:
        print(f'L1 (alpha\'alpha)_{c} =', pstr(prod.get(c, {})))
    prod2 = cmul(al, alp)
    for c in K4:
        print(f'L1 (alpha alpha\')_{c} =', pstr(prod2.get(c, {})))
    Da = det4(rmatrix(al))
    Dap = det4(rmatrix(alp))
    print('L1 det R_alpha terms', len(Da), ' det R_alpha\' terms', len(Dap))
    print('L1 det R_alpha\' == det R_alpha:', Dap == Da)
    for c in K4:
        if psigma(c, Da) == Dap:
            print('L1 det R_alpha\' == sigma_' + c + '(det R_alpha)')
    print('L1 det R_alpha =', pstr(Da, 120))

    # ---- certificates for the symmetric-piece theorem ----
    Nsym = prod['e']
    Msym = prod['C']
    for c in K4:
        assert psigma(c, Nsym) == Nsym
    print('C1 N is K4-invariant: True')
    ident = padd(pmul(Nsym, Nsym), pscale(pmul(mono(1, 1, 1), pmul(Msym, Msym)), -1))
    print('C1 det R_alpha == N^2 - x*y*z*M^2 :', ident == Da)
    assert ident == Da
    # exponent parity classes: pieces, N, mu = (xyz)^(1/2) M
    # every monomial of a piece has doubled exponents in a fixed class mod 2:
    # p0=x^-1/2 y^-1/2 p -> (1,1,0), q0=y^1/2 q -> (0,1,0), r0=x^-1/2 r -> (1,0,0), s0 -> (0,0,0);
    # sign changes preserve classes, so a product term's class is prefactor + sum of symbol classes
    SYMPAR = {'P0': (1, 1, 0), 'Q0': (0, 1, 0), 'R0': (1, 0, 0), 'S0': (0, 0, 0)}
    def parities(p):
        out = set()
        for (m, s), v in p.items():
            cl = [m[i] % 2 for i in range(3)]
            for nm, g in s:
                for i in range(3):
                    cl[i] = (cl[i] + SYMPAR[nm][i]) % 2
            out.add(tuple(cl))
        return sorted(out)
    print('C1 exponent parity classes (doubled mod 2): p0^A*p0-type N', parities(Nsym),
          ' mu=(xyz)^(1/2)M', parities(pmul(h(1, 1, 1), Msym)))
    assert parities(Nsym) == [(0, 0, 0)] and parities(pmul(h(1, 1, 1), Msym)) == [(1, 1, 1)]
    # R_{uv} = R_v R_u on generic elements (criterion multiplicativity)
    for nm in ('U', 'V'):
        pass
    u = elem(sym('p'), sym('q'), sym('r'), sym('s'))
    v = elem(sym('P'), sym('Q'), sym('R'), sym('S'))
    Muv = rmatrix(cmul(u, v))
    Mu, Mv = rmatrix(u), rmatrix(v)
    MvMu = {(i, j): padd(*[pmul(Mu[(i, k)], Mv[(k, j)]) for k in K4]) for i in K4 for j in K4}
    print('C2 R_{uv} = R_u R_v as matrices (row c, col cd):', Muv == MvMu)
    # Murray shapes give symmetric pieces (f_i functions of z only are ab-invariant)
    for i in range(1, 8):
        ABINV.add(f'f{i}')
    f = {i: sym(f'f{i}') for i in range(1, 8)}
    mp = pmul(pmul(poly([(1, 0, 0, 0), (1, 1, 0, 0)]), poly([(1, 0, 0, 0), (1, 0, 1, 0)])), f[1])
    mq = padd(pmul(pmul(poly([(1, 0, 0, 0), (1, 1, 0, 0)]), poly([(1, -1, 0, 0), (1, 0, -1, 0)])), f[2]),
              pmul(poly([(1, 0, 0, 0), (1, 0, -1, 0)]), f[3]))
    mr = padd(pmul(pmul(poly([(1, 0, 0, 0), (1, 0, -1, 0)]), poly([(1, 1, 0, 0), (1, 0, 1, 0)])), f[4]),
              pmul(poly([(1, 0, 0, 0), (1, 1, 0, 0)]), f[5]))
    ms_ = padd(pmul(poly([(1, 1, 0, 0), (4, 0, 0, 0), (1, -1, 0, 0), (1, 0, 1, 0), (1, 0, -1, 0)]), f[6]), f[7])
    mp0, mq0, mr0, ms0 = pmul(h(-1, -1, 0), mp), pmul(h(0, 1, 0), mq), pmul(h(-1, 0, 0), mr), ms_
    print('C3 Murray shape pieces ab-invariant:', all(psigma('C', g) == g for g in (mp0, mq0, mr0, ms0)))
    # Murray's u' (node murray-z-only-ansatz-has-no-char0-units) equals Gardam's alpha' on these pieces
    al_m, alp_m = lemma1(mp0, mq0, mr0, ms0)
    ok_pieces = (al_m == elem(mp, mq, mr, ms_))
    up_murray = elem(pmul(mono(-1, 0, 0), psigma('A', mp)), pscale(pmul(mono(-1, 0, 0), mq), -1),
                     pscale(pmul(mono(0, -1, 0), mr), -1), pmul(mono(0, 0, -1), psigma('A', ms_)))
    print('C3 alpha from pieces == Murray element:', ok_pieces, ' alpha\' == Murray u\':', alp_m == up_murray)
    json.dump({'det_generic_terms': len(D), 'det_sym_terms': len(Da), 'identity_det_eq_N2_minus_xyzM2': ident == Da},
              open('cp-certs.json', 'w'))
    print('DONE-CERTS')
