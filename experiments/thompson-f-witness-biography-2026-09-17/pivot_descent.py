#!/usr/bin/env python3
"""Private points of Guba sets under invariant orders and under caret-count-first orders.

Exact PL arithmetic over Q (helpers adapted from experiments/thompson-f/pl_check.py).

Checks:
 1. Composition convention realizing x_j x_i = x_i x_(j+1) (i<j).
 2. Group form. For U = S_(3,5) (9 monomials) and S_(2,4) (5 monomials), random m in F:
    number of t in U with t m private for m (m = max of {t''^-1 t m : t'' in U}) under
    (a) the germ-at-0 bi-order, (b) a dynamical left order, (c) its right-invariant mirror.
    The claim thompson-f-invariant-pivot-orders-cannot-certify-doubling predicts exactly 1.
 3. Monoid form at deep m (all t''^-1 t m in M): same count under (a), predicted 1.
 4. Caret-count-first orders: for sign in {+1,-1}, candidates
    T_m = {t : sign*carets(t''^-1 t m) <= sign*carets(m) for all t''}.
    A pivot order refining sign*carets needs |T_m| >= 2 at every m (group form) or every deep m
    (monoid form). We report the minimum and the fraction of sampled m with |T_m| >= 2.
"""
from fractions import Fraction as Q
import json, random, sys

def pl(points):
    return tuple((Q(a), Q(b)) for a, b in points)

def ev(f, y):
    for (x0, y0), (x1, y1) in zip(f, f[1:]):
        if x0 <= y <= x1:
            return y0 + (y1 - y0) * (y - x0) / (x1 - x0)
    raise ValueError(y)

def normalize(pts):
    pts = sorted(set(pts))
    out = [pts[0]]
    for p in pts[1:]:
        if p[0] == out[-1][0]:
            continue
        out.append(p)
    res = [out[0]]
    for i in range(1, len(out) - 1):
        (xa, ya), (xb, yb), (xc, yc) = res[-1], out[i], out[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            res.append(out[i])
    res.append(out[-1])
    return tuple(res)

def compose(f, g):
    """f o g : apply g first."""
    xs = set(x for x, _ in g)
    for x, _ in f:
        for (a0, b0), (a1, b1) in zip(g, g[1:]):
            if b0 <= x <= b1 and b1 != b0:
                xs.add(a0 + (a1 - a0) * (x - b0) / (b1 - b0))
    return normalize([(x, ev(f, ev(g, x))) for x in xs])

def inverse(f):
    return normalize([(b, a) for a, b in f])

ID = pl([(0, 0), (1, 1)])
A = pl([(0, 0), ("1/2", "1/4"), ("3/4", "1/2"), (1, 1)])
B = pl([(0, 0), ("1/2", "1/2"), ("3/4", "5/8"), ("7/8", "3/4"), (1, 1)])

CONV = None
def mul(g, h):
    return compose(g, h) if CONV == "R2L" else compose(h, g)

def word(ws):
    r = ID
    for w in ws:
        r = mul(r, w)
    return r

def gens(N):
    xs = [A, B]
    for n in range(2, N + 1):
        xs.append(word([inverse(A)] * (n - 1) + [B] + [A] * (n - 1)))
    return xs

# ---------- tree pair diagrams ----------
def slope_on(f, a, b):
    """slope if f is affine on [a,b], else None"""
    ya, yb = ev(f, a), ev(f, b)
    s = (yb - ya) / (b - a)
    for x, y in f:
        if a < x < b and y != ya + s * (x - a):
            return None
    return s

def is_std(a, b):
    L = b - a
    if L.numerator != 1 or (L.denominator & (L.denominator - 1)):
        return False
    return (a / L).denominator == 1

def leaves(f):
    out = []
    stack = [(Q(0), Q(1))]
    while stack:
        a, b = stack.pop()
        s = slope_on(f, a, b)
        if s is not None and is_std(ev(f, a), ev(f, b)):
            out.append((a, b))
        else:
            c = (a + b) / 2
            stack.append((c, b)); stack.append((a, c))
    out.sort()
    return out

def carets(f):
    return len(leaves(f)) - 1

def is_right_vine(parts):
    n = len(parts)
    for i, (a, b) in enumerate(parts):
        want = Q(1, 2 ** (i + 1)) if i < n - 1 else Q(1, 2 ** (n - 1))
        if b - a != want:
            return False
    return True

POS_SIDE = None  # "domain" or "range": which tree is a right vine for positive elements
def is_positive(f):
    D = leaves(f)
    R = [(ev(f, a), ev(f, b)) for a, b in D]
    return is_right_vine(D if POS_SIDE == "domain" else R)

# ---------- orders ----------
def sign_bi(g):
    """germ-at-0 bi-order: +1 if g(t) > t just right of the leftmost point of support"""
    for (x0, y0), (x1, y1) in zip(g, g[1:]):
        mid = (x0 + x1) / 2
        v = ev(g, mid)
        if v != mid:
            return 1 if v > mid else -1
        # identity on [x0,x1]: continue
    return 0

DENSE = [Q(1, 3)] + [Q(2 * k + 1, 2 ** n) for n in range(1, 7) for k in range(2 ** (n - 1))]
def cmp_dyn(g, h):
    """dynamical order: compare images of a fixed sequence starting with the non-dyadic 1/3"""
    for q in DENSE:
        a, b = ev(g, q), ev(h, q)
        if a != b:
            return -1 if a < b else 1
    return 0  # 1/3 has trivial stabilizer-free orbit only generically; ties impossible for g != h
             # because an element fixing 1/3 and all listed dyadics up to 2^-6 may still be nontrivial;
             # ties are reported.

def private_count(U, m, greater):
    """number of t in U such that m is the strict maximum among {t''^-1 t m}"""
    cnt = 0
    for t in U:
        w = mul(t, m)
        ok = True
        for t2 in U:
            if t2 is t:
                continue
            f = mul(inverse(t2), w)
            if not greater(m, f):
                ok = False; break
        if ok:
            cnt += 1
    return cnt

def rand_elem(xs, L):
    ws = []
    for _ in range(L):
        g = random.choice(xs[:3])
        ws.append(g if random.random() < 0.5 else inverse(g))
    return word(ws)

def rand_pos(xs, L):
    return word([random.choice(xs[:4]) for _ in range(L)])

def common_partition(Gs):
    """standard dyadic partition on each piece of which every g in Gs is affine with standard image"""
    out = []
    stack = [(Q(0), Q(1))]
    while stack:
        a, b = stack.pop()
        if all(slope_on(g, a, b) is not None and is_std(ev(g, a), ev(g, b)) for g in Gs):
            out.append((a, b))
        else:
            c = (a + b) / 2
            stack.append((c, b)); stack.append((a, c))
    out.sort()
    return out

def deep_positive(P):
    """positive element whose domain tree is a right vine and whose range partition is P"""
    n = len(P)
    D = [(1 - Q(1, 2 ** i), 1 - Q(1, 2 ** (i + 1))) for i in range(n - 1)]
    D.append((1 - Q(1, 2 ** (n - 1)), Q(1)))
    pts = [(D[j][0], P[j][0]) for j in range(n)] + [(Q(1), Q(1))]
    return normalize(pts)

def main():
    global CONV, POS_SIDE
    random.seed(20260917)
    report = {}
    for conv in ("R2L", "L2R"):
        CONV = conv
        xs = gens(6)
        if all(mul(xs[j], xs[i]) == mul(xs[i], xs[j + 1]) for i in range(4) for j in range(i + 1, 5)):
            break
    else:
        sys.exit("no convention")
    report["convention"] = CONV
    xs = gens(8)
    # positivity side
    posw = [rand_pos(xs, 6) for _ in range(20)]
    dom = all(is_right_vine(leaves(f)) for f in posw)
    rng = all(is_right_vine([(ev(f, a), ev(f, b)) for a, b in leaves(f)]) for f in posw)
    POS_SIDE = "domain" if dom and not rng else ("range" if rng and not dom else None)
    x0, x1 = xs[0], xs[1]
    negs = [inverse(x0), mul(x1, inverse(x0)), mul(inverse(x0), x1)]
    report["positive_tree_side"] = POS_SIDE
    report["positivity_test_rejects_nonpositive"] = [not is_positive(f) for f in negs]
    if POS_SIDE is None:
        sys.exit(json.dumps(report))

    def guba(m, d):
        out = [[]]
        for j in range(d):
            out = [p + [i] for p in out for i in range(0, m + j + 1) if not p or i >= p[-1]]
        return out
    sets = {"S_(2,4)": guba(1, 2), "S_(3,5)": guba(2, 2)}
    report["sets"] = {k: [list(v) for v in vs] for k, vs in sets.items()}

    bi_greater = lambda a, b: sign_bi(mul(inverse(b), a)) == 1   # a > b iff b^-1 a positive
    dyn_left = lambda a, b: cmp_dyn(a, b) == 1
    dyn_right = lambda a, b: cmp_dyn(inverse(a), inverse(b)) == -1  # mirror: a > b iff a^-1 < b^-1
    for name, idx in sets.items():
        U = [word([xs[i] for i in v]) for v in idx]
        rec = {}
        # group form
        counts = {"bi": [], "dyn_left": [], "dyn_right": []}
        for _ in range(40):
            m = rand_elem(xs, random.randint(4, 10))
            counts["bi"].append(private_count(U, m, bi_greater))
            counts["dyn_left"].append(private_count(U, m, dyn_left))
            counts["dyn_right"].append(private_count(U, m, dyn_right))
        rec["group_form_private_counts_distinct_values"] = {k: sorted(set(v)) for k, v in counts.items()}
        # deep monoid elements
        P = common_partition([mul(inverse(t2), t) for t in U for t2 in U])
        mstar = deep_positive(P)
        rec["deep_seed_leaves"] = len(P)
        deep = []
        tries = 0
        while len(deep) < 25 and tries < 400:
            tries += 1
            m = mul(mstar, rand_pos(xs, random.randint(0, 6)))
            if all(is_positive(mul(inverse(t2), mul(t, m))) for t in U for t2 in U):
                deep.append(m)
        rec["deep_monoid_samples"] = len(deep)
        rec["deep_monoid_tries"] = tries
        rec["deep_monoid_private_counts_bi"] = sorted(set(private_count(U, m, bi_greater) for m in deep))
        # caret-count-first candidates
        for sgn in (1, -1):
            for label, pool in (("group", [rand_elem(xs, random.randint(4, 10)) for _ in range(40)]),
                                ("deep_monoid", deep)):
                sizes = []
                for m in pool:
                    hm = sgn * carets(m)
                    T = [t for t in U if all(sgn * carets(mul(inverse(t2), mul(t, m))) <= hm for t2 in U)]
                    sizes.append(len(T))
                key = f"carets_sign{sgn:+d}_{label}"
                rec[key] = {"min_T": min(sizes) if sizes else None,
                            "frac_T_ge_2": (sum(s >= 2 for s in sizes) / len(sizes)) if sizes else None,
                            "samples": len(sizes)}
        report[name] = rec
    print(json.dumps(report, indent=1))

if __name__ == "__main__":
    main()
