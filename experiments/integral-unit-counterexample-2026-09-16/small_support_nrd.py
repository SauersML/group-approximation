#!/usr/bin/env python3
"""Small-support analysis of units of Z[P], P the Promislow group (exact, pure python).

Conventions are those of research/artifacts/promislow-reduced-norm-cp.py
(Gardam's affine model, coefficients on the left, x=a^2, y=b^2, z=(ab)^2,
u = p + q a + r b + s ab, sigma_A(x,y,z) = (x, 1/y, 1/z), sigma_B = (1/x, y, 1/z),
sigma_C = (1/x, 1/y, z)).  Laurent polynomials are dicts {(i,j,k): int}.

Parts
  V  validate the quartic reduced-norm formula against the engine's det4.
  J  census in the box {-R..R}^3: every nonzero element of (XY,XZ,YZ)Z[L]
     (X=x+1, ...) has >= 4 terms, and the 4-term ones are
     c * l * (1 - w1(-x,-y,-z)) * (1 - w2(-x,-y,-z)), w1 an axis monomial,
     w2 a nonzero monomial not involving that axis.
  N9 all normalized support-9 candidates  eps + c1*q0*a + c2*r0*b  (and the
     two other coset pairs), q0, r0 4-term elements of J_L supported in the box;
     certify that the reduced norm is not a constant for any nonzero integers
     c1, c2 (certificate: an L-monomial m != 1 whose coefficient, a polynomial in
     X1=c1^2, X2=c2^2, has no solution with X1, X2 > 0; see cert()).
Run:  timeout 600 python3 small_support_nrd.py R
"""
import sys, itertools, importlib.util, random, json, time
from collections import defaultdict
from fractions import Fraction

HERE = __file__.rsplit('/', 1)[0]
ROOT = HERE + '/../..'

# ---------------- Laurent polynomials ----------------
def padd(*ps):
    out = defaultdict(int)
    for p in ps:
        for k, v in p.items():
            out[k] += v
    return {k: v for k, v in out.items() if v}
def pscale(p, c):
    return {k: v * c for k, v in p.items()} if c else {}
def pmul(*ps):
    acc = {(0, 0, 0): 1}
    for p in ps:
        out = defaultdict(int)
        for m1, v1 in acc.items():
            for m2, v2 in p.items():
                out[(m1[0] + m2[0], m1[1] + m2[1], m1[2] + m2[2])] += v1 * v2
        acc = {k: v for k, v in out.items() if v}
        if not acc:
            return {}
    return acc
SGN = {'e': (1, 1, 1), 'A': (1, -1, -1), 'B': (-1, 1, -1), 'C': (-1, -1, 1)}
def sig(c, p):
    s = SGN[c]
    return {(s[0] * m[0], s[1] * m[1], s[2] * m[2]): v for m, v in p.items()}
def mono(i, j, k, c=1):
    return {(i, j, k): c}
X1, Y1, Z1 = mono(1, 0, 0), mono(0, 1, 0), mono(0, 0, 1)
Xm, Ym, Zm = mono(-1, 0, 0), mono(0, -1, 0), mono(0, 0, -1)

def nrd(p, q, r, s):
    """quartic reduced norm, formula of promislow-group-ring-units-are-constant-reduced-norm"""
    A = lambda f: sig('A', f)
    B = lambda f: sig('B', f)
    C = lambda f: sig('C', f)
    T = [
        (+1, [A(p), B(p), C(p), p]), (-1, [A(p), B(p), C(s), s, Z1]), (-1, [A(p), C(p), B(r), r, Y1]),
        (-1, [A(p), p, B(q), C(q), Xm]), (+1, [A(p), B(q), r, C(s), Xm, Y1]), (+1, [A(p), C(q), B(r), s, Z1]),
        (-1, [B(p), C(p), A(q), q, X1]), (-1, [B(p), p, A(r), C(r), Ym]), (+1, [B(p), A(q), C(r), s, X1, Ym]),
        (+1, [B(p), q, A(r), C(s), Z1]), (-1, [C(p), p, A(s), B(s), Zm]), (+1, [C(p), A(q), r, B(s), Zm]),
        (+1, [C(p), q, B(r), A(s), X1, Y1]), (+1, [p, B(q), C(r), A(s), Zm]), (+1, [p, C(q), A(r), B(s), Xm, Ym]),
        (+1, [A(q), B(q), C(q), q]), (-1, [A(q), B(q), C(r), r, Zm]), (-1, [A(q), C(q), B(s), s, Ym]),
        (-1, [B(q), q, A(s), C(s), Y1]), (-1, [C(q), q, A(r), B(r), Z1]), (+1, [A(r), B(r), C(r), r]),
        (-1, [A(r), r, B(s), C(s), Xm]), (-1, [B(r), C(r), A(s), s, X1]), (+1, [A(s), B(s), C(s), s]),
    ]
    return padd(*[pscale(pmul(*fs), c) for c, fs in T])

def load_engine():
    spec = importlib.util.spec_from_file_location('cp', ROOT + '/research/artifacts/promislow-reduced-norm-cp.py')
    cp = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cp)
    return cp

def part_V(ntests=25, seed=1):
    cp = load_engine()
    rng = random.Random(seed)
    def rp():
        return padd(*[mono(rng.randint(-1, 1), rng.randint(-1, 1), rng.randint(-1, 1), rng.randint(-2, 2)) for _ in range(rng.randint(0, 3))])
    def toeng(p):
        return {((2 * m[0], 2 * m[1], 2 * m[2]), ()): v for m, v in p.items()}
    ok = 0
    for _ in range(ntests):
        p, q, r, s = rp(), rp(), rp(), rp()
        D = cp.det4(cp.rmatrix(cp.elem(toeng(p), toeng(q), toeng(r), toeng(s))))
        if D == toeng(nrd(p, q, r, s)):
            ok += 1
    return ok, ntests

def nrd_terms(p, q, r, s):
    """the 24 terms as (sign, [(label, poly)]) with labels in 'pqrs' (monomials x,y,z labelled 'm')"""
    lab = {'p': p, 'q': q, 'r': r, 's': s}
    spec = [
        '+ Ap Bp Cp p', '- Ap Bp Cs s Z', '- Ap Cp Br r Y', '- Ap p Bq Cq x', '+ Ap Bq r Cs x Y', '+ Ap Cq Br s Z',
        '- Bp Cp Aq q X', '- Bp p Ar Cr y', '+ Bp Aq Cr s X y', '+ Bp q Ar Cs Z', '- Cp p As Bs z', '+ Cp Aq r Bs z',
        '+ Cp q Br As X Y', '+ p Bq Cr As z', '+ p Cq Ar Bs x y', '+ Aq Bq Cq q', '- Aq Bq Cr r z', '- Aq Cq Bs s y',
        '- Bq q As Cs Y', '- Cq q Ar Br Z', '+ Ar Br Cr r', '- Ar r Bs Cs x', '- Br Cr As s X', '+ As Bs Cs s',
    ]
    MON = {'X': X1, 'Y': Y1, 'Z': Z1, 'x': Xm, 'y': Ym, 'z': Zm}
    out = []
    for t in spec:
        toks = t.split()
        sign = 1 if toks[0] == '+' else -1
        facs = []
        for tk in toks[1:]:
            if tk in MON:
                facs.append(('m', MON[tk]))
            elif len(tk) == 2:
                facs.append((tk[1], sig(tk[0], lab[tk[1]])))
            else:
                facs.append((tk, lab[tk]))
        out.append((sign, facs))
    return out

def check_terms_formula(ntests=10, seed=2):
    rng = random.Random(seed)
    def rp():
        return padd(*[mono(rng.randint(-1, 1), rng.randint(-1, 1), rng.randint(-1, 1), rng.randint(-2, 2)) for _ in range(rng.randint(0, 3))])
    for _ in range(ntests):
        p, q, r, s = rp(), rp(), rp(), rp()
        tot = padd(*[pscale(pmul(*[f for _, f in facs]), sg) for sg, facs in nrd_terms(p, q, r, s)])
        if tot != nrd(p, q, r, s):
            return False
    return True

def pieces_const_p(eps, comps):
    """p = eps (+-1); comps: dict label->poly for exactly the nonzero components among q,r,s.
    Returns {(e1,e2,...): poly} where the key counts the degree in each component (in the order of sorted labels)."""
    labs = sorted(comps)
    full = {'p': {(0, 0, 0): eps}, 'q': {}, 'r': {}, 's': {}}
    full.update(comps)
    out = defaultdict(dict)
    for sg, facs in nrd_terms(full['p'], full['q'], full['r'], full['s']):
        prod = pmul(*[f for _, f in facs])
        if not prod:
            continue
        key = tuple(sum(1 for l, _ in facs if l == lb) for lb in labs)
        out[key] = padd(out[key], pscale(prod, sg))
    return {k: v for k, v in out.items() if v}

# ---------------- J_L census ----------------
def box(R):
    return [(i, j, k) for i in range(-R, R + 1) for j in range(-R, R + 1) for k in range(-R, R + 1)]

def kernel_full_support(S):
    """Does a rational vector with ALL coordinates nonzero, supported on S, have vanishing
    twisted plane sums sum_{m_d = v} (-1)^{sum of other coords} c_m = 0 for d = 0,1,2 and all v?"""
    S = list(S)
    rows = []
    for d in range(3):
        for v in set(m[d] for m in S):
            row = []
            for m in S:
                if m[d] == v:
                    row.append(Fraction((-1) ** (sum(m) - m[d])))
                else:
                    row.append(Fraction(0))
            rows.append(row)
    n = len(S)
    # row reduce
    M = [r[:] for r in rows]
    piv = []
    ri = 0
    for c in range(n):
        pr = next((i for i in range(ri, len(M)) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[ri], M[pr] = M[pr], M[ri]
        pv = M[ri][c]
        M[ri] = [x / pv for x in M[ri]]
        for i in range(len(M)):
            if i != ri and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[ri])]
        piv.append(c)
        ri += 1
    free = [c for c in range(n) if c not in piv]
    if not free:
        return False
    # coordinate c vanishes on kernel iff c is a pivot whose row has zeros in all free columns
    for i, c in enumerate(piv):
        if all(M[i][f] == 0 for f in free):
            return False
    return True

def hat(w):
    """w(-x,-y,-z) sign"""
    return (-1) ** (abs(w[0]) + abs(w[1]) + abs(w[2]))

def four_term_elements(R):
    """all 4-term elements of J_L supported in the box, up to sign: l*(1 - hat w1)(1 - hat w2)"""
    pts = set(box(R))
    seen = {}
    rng = range(-2 * R, 2 * R + 1)
    for l in box(R):
        for ax in range(3):
            for t in rng:
                if t == 0:
                    continue
                w1 = tuple(t if d == ax else 0 for d in range(3))
                for w2 in itertools.product(rng, repeat=3):
                    if w2[ax] != 0 or w2 == (0, 0, 0):
                        continue
                    supp = [l, tuple(l[d] + w1[d] for d in range(3)), tuple(l[d] + w2[d] for d in range(3)),
                            tuple(l[d] + w1[d] + w2[d] for d in range(3))]
                    if not all(m in pts for m in supp):
                        continue
                    el = pmul(mono(*l), padd({(0, 0, 0): 1}, mono(*w1, -hat(w1))), padd({(0, 0, 0): 1}, mono(*w2, -hat(w2))))
                    key = frozenset(el)
                    # normalize sign: coefficient at lexicographically smallest monomial positive
                    mn = min(el)
                    if el[mn] < 0:
                        el = pscale(el, -1)
                    if key in seen:
                        assert seen[key] == el, (seen[key], el)
                    else:
                        seen[key] = el
    return list(seen.values())

def in_JL(p):
    return all(sum(v * (-1) ** (sum(m) - m[d]) for m, v in p.items() if m[d] == val) == 0
               for d in range(3) for val in set(m[d] for m in p))

def part_J(R=1):
    pts = box(R)
    counts = {}
    four = set()
    for n in range(1, 5):
        c = 0
        for S in itertools.combinations(pts, n):
            if kernel_full_support(S):
                c += 1
                if n == 4:
                    four.add(frozenset(S))
        counts[n] = c
    gen = four_term_elements(R)
    genset = set(frozenset(e) for e in gen)
    return counts, len(four), len(genset), four == genset, all(in_JL(e) for e in gen)

# ---------------- N9: support-9 candidates ----------------
PAIRS = [('q', 'r'), ('q', 's'), ('r', 's')]   # cosets (a,b), (a,ab), (b,ab)
UNK = ['U1', 'U2', 'U3', 'U4', 'U5']           # X1^2, X2^2, X1, X2, X1*X2

def coeff_table(pieces):
    """{m: [c_U1..c_U5]} from pieces keyed by degree pairs (4,0),(0,4),(2,0),(0,2),(2,2)"""
    idx = {(4, 0): 0, (0, 4): 1, (2, 0): 2, (0, 2): 3, (2, 2): 4, (0, 0): None}
    tab = defaultdict(lambda: [0] * 5)
    const = 0
    for key, poly in pieces.items():
        if key not in idx:
            raise ValueError('unexpected degree key %r' % (key,))
        if idx[key] is None:
            const = poly.get((0, 0, 0), 0)
            assert set(poly) <= {(0, 0, 0)}
            continue
        for m, v in poly.items():
            tab[m][idx[key]] += v
    return tab, const

def cert(eps, labs, e1, e2):
    """Certificate that eps + c1*e1*g1 + c2*e2*g2 (components labs) is not a unit for any
    nonzero integers c1, c2.  Returns (kind, data) or ('SURVIVOR', data)."""
    pieces = pieces_const_p(eps, {labs[0]: e1, labs[1]: e2})
    tab, const = coeff_table(pieces)
    assert const == 1
    # kind 1: a monomial m != 0 whose coefficient polynomial has all coefficients of one sign
    for m in sorted(tab):
        if m == (0, 0, 0):
            continue
        cs = tab[m]
        if any(cs) and (all(c >= 0 for c in cs) or all(c <= 0 for c in cs)):
            return ('sign', (m, cs))
    # kind 2: exact linear algebra in U1..U5, then the quadric constraints
    rows = [tab[m] for m in sorted(tab) if m != (0, 0, 0)]
    c0 = tab[(0, 0, 0)] if (0, 0, 0) in tab else [0] * 5
    return ('SURVIVOR', {'rows': rows, 'c0': c0})

def solve_survivor(rows, c0, bound=None):
    """exact: all positive integers X1, X2 (perfect squares) with rows.U = 0 and c0.U in {0,-2}.
    Uses sympy on the polynomial system; returns list of solutions."""
    import sympy as sp
    X1s, X2s = sp.symbols('X1 X2', positive=True)
    U = [X1s ** 2, X2s ** 2, X1s, X2s, X1s * X2s]
    eqs = list({sp.expand(sum(c * u for c, u in zip(r, U))) for r in rows})
    eqs = [e for e in eqs if e != 0]
    sols = []
    for target in (0, -2):
        E0 = sp.expand(sum(c * u for c, u in zip(c0, U)) - target)
        system = eqs + ([E0] if E0 != 0 else [])
        G = sp.groebner(system, X1s, X2s, order='lex')
        if list(G) == [1]:
            continue
        for sol in sp.solve(list(G), [X1s, X2s], dict=True):
            sols.append((target, sol))
    return sols

def part_N9(R=1, pairs=PAIRS, log=None):
    els = four_term_elements(R)
    stats = defaultdict(int)
    survivors = []
    t0 = time.time()
    for labs in pairs:
        for e1 in els:
            for e2 in els:
                kind, data = cert(1, labs, e1, e2)
                stats[kind] += 1
                if kind == 'SURVIVOR':
                    survivors.append((labs, e1, e2, data))
    return els, stats, survivors, time.time() - t0

# fast version with per-element caches (checked against cert() on random samples)
_SPEC_CACHE = {}
def _spec_split(labs):
    """for the pair labs, the nonzero terms (p = constant, third component 0) as
    (sign, factors of labs[0] (conj letters), factors of labs[1], monomial exponent)"""
    if labs in _SPEC_CACHE:
        return _SPEC_CACHE[labs]
    probe = {'q': {(0, 0, 0): 1}, 'r': {(0, 0, 0): 1}, 's': {(0, 0, 0): 1}}
    third = [l for l in 'qrs' if l not in labs][0]
    probe[third] = {}
    out = []
    for sg, facs in nrd_terms({(0, 0, 0): 1}, probe['q'], probe['r'], probe['s']):
        if any(l == third for l, _ in facs):
            continue
        out.append(sg)
    # re-derive with labelled conjugation letters by parsing the spec strings
    spec = [
        '+ Ap Bp Cp p', '- Ap Bp Cs s Z', '- Ap Cp Br r Y', '- Ap p Bq Cq x', '+ Ap Bq r Cs x Y', '+ Ap Cq Br s Z',
        '- Bp Cp Aq q X', '- Bp p Ar Cr y', '+ Bp Aq Cr s X y', '+ Bp q Ar Cs Z', '- Cp p As Bs z', '+ Cp Aq r Bs z',
        '+ Cp q Br As X Y', '+ p Bq Cr As z', '+ p Cq Ar Bs x y', '+ Aq Bq Cq q', '- Aq Bq Cr r z', '- Aq Cq Bs s y',
        '- Bq q As Cs Y', '- Cq q Ar Br Z', '+ Ar Br Cr r', '- Ar r Bs Cs x', '- Br Cr As s X', '+ As Bs Cs s',
    ]
    MONE = {'X': (1, 0, 0), 'Y': (0, 1, 0), 'Z': (0, 0, 1), 'x': (-1, 0, 0), 'y': (0, -1, 0), 'z': (0, 0, -1)}
    res = []
    for t in spec:
        toks = t.split()
        sg = 1 if toks[0] == '+' else -1
        f1, f2, mon, bad = [], [], [0, 0, 0], False
        for tk in toks[1:]:
            if tk in MONE:
                mon = [mon[d] + MONE[tk][d] for d in range(3)]
                continue
            letter, lab = (tk[0], tk[1]) if len(tk) == 2 else ('e', tk)
            if lab == 'p':
                continue
            if lab == labs[0]:
                f1.append(letter)
            elif lab == labs[1]:
                f2.append(letter)
            else:
                bad = True
        if not bad:
            res.append((sg, tuple(f1), tuple(f2), tuple(mon)))
    _SPEC_CACHE[labs] = res
    return res

def _conj_prod(e, letters):
    return pmul(*[sig(l, e) for l in letters]) if letters else {(0, 0, 0): 1}

def cert_fast(labs, i1, i2, els, cache):
    terms = _spec_split(labs)
    tab = defaultdict(lambda: [0, 0, 0, 0, 0])
    for (sg, f1, f2, mon) in terms:
        d1, d2 = len(f1), len(f2)
        slot = {(4, 0): 0, (0, 4): 1, (2, 0): 2, (0, 2): 3, (2, 2): 4, (0, 0): None}[(d1, d2)]
        if slot is None:
            continue
        k1 = (f1, i1)
        if k1 not in cache:
            cache[k1] = _conj_prod(els[i1], f1)
        k2 = (f2, i2)
        if k2 not in cache:
            cache[k2] = _conj_prod(els[i2], f2)
        P1, P2 = cache[k1], cache[k2]
        for m1, v1 in P1.items():
            for m2, v2 in P2.items():
                tab[(m1[0] + m2[0] + mon[0], m1[1] + m2[1] + mon[1], m1[2] + m2[2] + mon[2])][slot] += sg * v1 * v2
    for m in sorted(tab):
        if m == (0, 0, 0):
            continue
        cs = tab[m]
        if any(cs) and (all(c >= 0 for c in cs) or all(c <= 0 for c in cs)):
            return ('sign', (m, cs))
    rows = [tab[m] for m in sorted(tab) if m != (0, 0, 0) and any(tab[m])]
    c0 = tab.get((0, 0, 0), [0] * 5)
    return ('SURVIVOR', {'rows': rows, 'c0': list(c0)})

def run_N9(R, pair_index, out_path):
    labs = PAIRS[pair_index]
    els = four_term_elements(R)
    cache = {}
    stats = defaultdict(int)
    survivors = []
    cert_monomial_hist = defaultdict(int)
    t0 = time.time()
    for i1 in range(len(els)):
        for i2 in range(len(els)):
            kind, data = cert_fast(labs, i1, i2, els, cache)
            stats[kind] += 1
            if kind == 'SURVIVOR':
                survivors.append({'e1': sorted([list(k), v] for k, v in els[i1].items()),
                                  'e2': sorted([list(k), v] for k, v in els[i2].items()),
                                  'rows': data['rows'], 'c0': data['c0']})
            else:
                cert_monomial_hist[str(data[1])] += 1
        # drop caches of the finished first element
        for k in [k for k in cache if k[1] == i1 and len(k[0]) and k[0] in ()]:
            del cache[k]
    res = {'R': R, 'pair': labs, 'cosets': {'q': 'a', 'r': 'b', 's': 'ab'}, 'num_four_term_elements': len(els),
           'num_ordered_pairs': len(els) ** 2, 'stats': dict(stats), 'num_survivors': len(survivors),
           'survivors': survivors[:200], 'sign_cert_coefficient_patterns': dict(cert_monomial_hist),
           'seconds': round(time.time() - t0, 1)}
    with open(out_path, 'w') as fh:
        json.dump(res, fh, indent=0)
    return res

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'V':
        print('Part V (engine det4 vs quartic formula):', part_V(40))
        print('term table reproduces formula:', check_terms_formula(20))
    elif mode == 'J':
        R = int(sys.argv[2])
        print('Part J census R=%d:' % R, part_J(R))
    elif mode == 'N9':
        R, pi = int(sys.argv[2]), int(sys.argv[3])
        res = run_N9(R, pi, HERE + '/log-N9-R%d-pair%d.json' % (R, pi))
        print({k: v for k, v in res.items() if k not in ('survivors', 'sign_cert_coefficient_patterns')})
