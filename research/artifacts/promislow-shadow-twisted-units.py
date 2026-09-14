#!/usr/bin/env python3
"""Twists u * sigma(u)^-1 of known nontrivial units of F_p[P] by the diagonal automorphisms of P,
and whether their three definite shadows are signed monomials (lane hl-promislow-case-a).

Imports research/artifacts/promislow-definite-shadows-residues.py (which imports
gardam-support-pair-gsp.py) for the affine model of P, Gardam's unit and the shadow maps.
An automorphism sigma_h is conjugation by h = diag(e1, e2, e3) (zero translation) whenever
h a h^-1 and h b h^-1 lie in P. Shadows of v = u sigma(u)^-1 are computed in D(F_p) as
shadow(u) * shadow(sigma(u))^-1, with X^-1 = N(X)^-1 (l0bar, -l1) for X of constant norm.
v is a trivial unit (lambda g) iff u = lambda g sigma(u); this is tested exactly.
"""
import sys, io, itertools, contextlib, importlib.util
here = sys.path[0]
sys.argv = ['res']
spec = importlib.util.spec_from_file_location('res', here + '/promislow-definite-shadows-residues.py')
R = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(R)
G = R.G
E = G.E

def gr_red(U, p):
    return {g: c % p for g, c in U.items() if c % p}

def gr_mul(U, V, p):
    out = {}
    for g, c in U.items():
        for h, d in V.items():
            k = G.mul(g, h)
            out[k] = (out.get(k, 0) + c * d) % p
    return {k: v for k, v in out.items() if v}

def trans(t):
    return ((1, 0, 0, t[0]), (0, 1, 0, t[1]), (0, 0, 1, t[2]), (0, 0, 0, 1))

def pqrs_to_gr(pqrs, p):
    reps = [R.REP['e'], R.REP['A'], R.REP['B'], R.REP['C']]
    out = {}
    for f, rep in zip(pqrs, reps):
        for (i, j, k), v in f.items():
            g = G.mul(trans((2 * i, 2 * j, -2 * k)), rep)
            out[g] = (out.get(g, 0) + v) % p
    return {g: v for g, v in out.items() if v}

def in_P(g):
    try:
        R.decompose(g)
        return True
    except Exception:
        return False

def sigma(h):
    H = ((h[0], 0, 0, 0), (0, h[1], 0, 0), (0, 0, h[2], 0), (0, 0, 0, 1))
    return lambda g: G.mul(G.mul(H, g), H)

def gr_apply(U, s):
    return {s(g): c for g, c in U.items()}

def dinv(X, p):
    N = R.dnorm(X, p)
    assert set(N) == {0}, ('norm not constant', N)
    ni = pow(N[0], -1, p)
    return (R.lred({k: ni * v for k, v in R.lbar(X[0]).items()}, p),
            R.lred({k: -ni * v for k, v in X[1].items()}, p))

def is_trivial_quotient(U, V, p):
    """True iff U = lambda g V for some lambda in F_p^x and g in P."""
    u0 = next(iter(U))
    for e1 in V:
        g = G.mul(u0, G.inv(e1))
        lam = U[u0] * pow(V[e1], -1, p) % p
        if gr_red({G.mul(g, h): lam * c for h, c in V.items()}, p) == U:
            return True
    return False

DIAG = [h for h in itertools.product((1, -1), repeat=3) if h != (1, 1, 1)]
VALID = [h for h in DIAG if in_P(sigma(h)(G.a)) and in_P(sigma(h)(G.b))]
print('valid diagonal automorphisms h:', VALID)
for h in VALID:
    s = sigma(h)
    print('  h=%s: sigma(a) in P, sigma(b) in P; sigma(a^2)=%s sigma(b^2)=%s' % (h, R.decompose(s(G.w(G.a, G.a))), R.decompose(s(G.w(G.b, G.b)))))

def twist_report(name, U, p, Uinv=None):
    rows = []
    SU = {}
    shU = {line: R.shadow(R.group_ring_to_pqrs(U, lambda c: c), line, p) for line in 'CAB'}
    for h in VALID:
        s = sigma(h)
        SUh = gr_red(gr_apply(U, s), p)
        mono = []
        for line in 'CAB':
            Xs = R.shadow(R.group_ring_to_pqrs(SUh, lambda c: c), line, p)
            Y = R.dmul(shU[line], dinv(Xs, p), p)
            mono.append(R.monomial_shadow(Y, p))
        nontriv = not is_trivial_quotient(U, SUh, p)
        extra = ''
        if Uinv is not None:
            V = gr_mul(U, gr_apply(Uinv, s), p)  # u * sigma(u^-1) = u * sigma(u)^-1
            chk = gr_mul(V, SUh, p) == gr_red(U, p)
            shV = [R.monomial_shadow(R.shadow(R.group_ring_to_pqrs(V, lambda c: c), line, p), p) for line in 'CAB']
            extra = ' | explicit v: |supp|=%d, v*sigma(u)==u: %s, monomial shadows C,A,B=%s' % (len(V), chk, shV)
        rows.append((h, mono, nontriv))
        print('  %s h=%s: monomial shadows of u sigma(u)^-1 on C,A,B = %s | nontrivial: %s%s' % (name, h, mono, nontriv, extra))
    return rows

# Gardam's unit of F_2[P]
coef2 = lambda c: sum(c.values()) % 2
alpha2 = gr_red({g: coef2(c) for g, c in G.alpha.items()}, 2)
beta2 = gr_red({g: coef2(c) for g, c in G.beta.items()}, 2)
print('Gardam F_2: |supp|=%d, alpha*beta==1: %s' % (len(alpha2), gr_mul(alpha2, beta2, 2) == {E: 1}))
summary = []
for h, mono, nt in twist_report('gardam', alpha2, 2, beta2):
    summary.append(('gardam', 2, h, all(mono), nt))

# Murray Theorem 3 units of F_d[P] (formulas as in promislow-definite-shadows-residues.py)
lp_add, lp_mul, mono, ONE, zp = R.lp_add, R.lp_mul, R.mono, R.ONE, R.zp
X_, Xi, Y_, Yi = mono(1, 0, 0), mono(-1, 0, 0), mono(0, 1, 0), mono(0, -1, 0)
for d in (3, 5, 7):
    for t_, w_ in itertools.product((-1, 0, 1, 2), (0, 1)):
        h_ = ONE
        for _ in range(d - 2):
            h_ = lp_mul(h_, lp_add(ONE, zp(1 - 2 * t_, -1)))
        f1 = lp_mul(lp_add(zp(t_), zp(1 - t_)), h_); f2 = lp_mul(zp(w_), h_)
        f3 = lp_mul(zp(w_), lp_add(ONE, zp(2 * t_ - 1)), h_); f4 = lp_mul(zp(w_ + t_), h_)
        f5 = lp_mul(zp(w_), lp_add(zp(t_), zp(1 - t_)), h_); f6 = h_; f7 = zp(2 * t_ - 1)
        p_ = lp_mul(lp_add(ONE, X_), lp_add(ONE, Y_), f1)
        q_ = lp_add(lp_mul(lp_add(ONE, X_), lp_add(Xi, Yi), f2), lp_mul(lp_add(ONE, Yi), f3))
        r_ = lp_add(lp_mul(lp_add(ONE, Yi), lp_add(X_, Y_), f4), lp_mul(lp_add(ONE, X_), f5))
        s_ = lp_add(lp_mul(lp_add(X_, mono(0, 0, 0, 4), Xi, Y_, Yi), f6), f7)
        U = pqrs_to_gr([p_, q_, r_, s_], d)
        name = 'murray(d=%d,t=%d,w=%d)' % (d, t_, w_)
        for h, mono_, nt in twist_report(name, U, d):
            summary.append((name, d, h, all(mono_), nt))

print('SUMMARY: nontrivial twisted units with all three shadows monomial:')
hits = [row for row in summary if row[3] and row[4]]
for row in hits:
    print('  HIT', row)
print('  hits: %d of %d twists' % (len(hits), len(summary)))
print('DONE')
