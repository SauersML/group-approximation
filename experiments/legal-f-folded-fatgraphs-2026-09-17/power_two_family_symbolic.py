"""Symbolic (all k >= 3) verification of the closed-form power-two certificates of
power_two_family_certificates.py for phi_k : a -> abb, b -> c a^k, c -> babb.

Positions are affine functions c0 + ck*k + ci*i of the family parameter k and a template
parameter i, over regions  k >= KMIN, lo(k) <= i <= hi(k)  with lo, hi affine in k. An affine
inequality g >= 0 holds on such a region iff it holds at the two corners at k = KMIN and along the
two recession directions (1, lo_k) and (1, hi_k); this is what `nonneg` checks (exact rationals).

Input data (transcribed from the -proof note):
  SEGS     the four boundary circles as segments [start, end] with a periodic pattern;
  RULES    the pairing p as 15 affine rules (r13 of the note merged into r15 as its j = 0 case);
  JUNCTION f^2-junction darts and minus darts;
  TEMPLATES the 19 vertex templates (12 of valence 2, 7 of valence 4), darts in sigma order
           sigma(d) = nxt(p(d)).
Checks, for all k >= KMIN and all template parameters:
  (a) every sigma step: the dart lies in the domain of a rule for the whole region, the rule's
      parameter is an integer affine function, and nxt of its image equals the next template dart;
      the last step returns to the first dart;
  (b) labels of all template darts, read off the segment table (range and residue checks), and
      p pairs each dart with a dart carrying the inverse letter;
  (c) (L): labels at a vertex are in pairwise distinct gates {a},{b},{c},{A,C},{B};
      (2)/(3): a vertex containing a junction dart has valence 2 and contains only one junction dart;
      (4): at most one minus dart per vertex, and every rule with a minus dart pairs it with a plus dart;
  (d) the size sum of the templates is 12k + 24 (all darts) and the vertex count is 4k + 10;
      the rules define 6k + 12 pairs (so, all darts being in some rule domain, p is an involution).
Every check must hold on the whole region of its template; Q5' is the last member (j = k-2) of the
family Q5, listed separately because its third dart is the final letter B of P1.
Coverage (every dart lies in some template) is the partition table of the -proof note, and it is
cross-checked numerically, together with equality of templates and orbits, for 3 <= k <= KNUM.

usage: python3 power_two_family_symbolic.py KNUM out.log
"""
import sys, importlib.util, os
from fractions import Fraction as Fr

KMIN = 3
KNUM, OUT = int(sys.argv[1]), sys.argv[2]
log = open(OUT, "w")


def say(*a):
    s = " ".join(str(x) for x in a)
    print(s); log.write(s + "\n"); log.flush()


def A(c0=0, ck=0, ci=0):
    return (Fr(c0), Fr(ck), Fr(ci))


def add(u, v):
    return tuple(x + y for x, y in zip(u, v))


def sub(u, v):
    return tuple(x - y for x, y in zip(u, v))


def subst(u, i_expr):
    """substitute i = i_expr (affine in k only) into u"""
    return (u[0] + u[2] * i_expr[0], u[1] + u[2] * i_expr[1], Fr(0))


# region: (lo, hi) affine in k (ci = 0)
def nonneg(g, reg):
    lo, hi = reg
    k = KMIN
    corners = [(k, lo[0] + lo[1] * k), (k, hi[0] + hi[1] * k)]
    if corners[1][1] < corners[0][1] or hi[1] < lo[1]:
        raise ValueError("empty or shrinking region")
    for kk, ii in corners:
        if g[0] + g[1] * kk + g[2] * ii < 0:
            return False
    for slope in (lo[1], hi[1]):
        if g[1] + g[2] * slope < 0:
            return False
    return True


def zero(g, reg):
    return nonneg(g, reg) and nonneg(tuple(-x for x in g), reg)


LEN = {"N1": A(2), "N2": A(2), "P1": A(10, 6), "P2": A(10, 6)}

# segments: (circle, start, end, pattern) with the pattern read from start
SEGS = [
    ("N1", A(0), A(1), "bc"), ("N2", A(0), A(1), "CB"),
    ("P1", A(0), A(-1, 1), "A"), ("P1", A(0, 1), A(0, 1), "C"), ("P1", A(1, 1), A(0, 2), "A"),
    ("P1", A(1, 2), A(1, 2), "C"), ("P1", A(2, 2), A(4, 2), "BBA"), ("P1", A(5, 2), A(4, 3), "A"),
    ("P1", A(5, 3), A(5, 3), "C"), ("P1", A(6, 3), A(8, 6), "BBA"), ("P1", A(9, 6), A(9, 6), "B"),
    ("P2", A(0), A(0), "b"), ("P2", A(1), A(3, 3), "abb"), ("P2", A(4, 3), A(4, 3), "c"),
    ("P2", A(5, 3), A(4, 4), "a"), ("P2", A(5, 4), A(7, 4), "abb"), ("P2", A(8, 4), A(8, 4), "c"),
    ("P2", A(9, 4), A(8, 5), "a"), ("P2", A(9, 5), A(9, 5), "c"), ("P2", A(10, 5), A(9, 6), "a"),
]

# pairing rules: ((circ, pos(k,t)), (circ, pos(k,t)), t-range (lo, hi) affine in k)
RULES = [
    (("P1", A(1, 1, 1)), ("P2", A(4, 4, -1)), (A(0), A(-1, 1))),
    (("P1", A(1, 2)), ("P2", A(4, 3)), (A(0), A(0))),
    (("P1", A(2, 2, 1)), ("P2", A(3, 3, -1)), (A(0), A(2))),
    (("P1", A(5, 2, 1)), ("P2", A(8, 5, -1)), (A(0), A(-1, 1))),
    (("P1", A(5, 3)), ("P2", A(8, 4)), (A(0), A(0))),
    (("P1", A(6, 3, 1)), ("P2", A(7, 4, -1)), (A(0), A(2))),
    (("N1", A(0)), ("P1", A(9, 3)), (A(0), A(0))),
    (("N1", A(1)), ("P1", A(0, 1)), (A(0), A(0))),
    (("N2", A(0)), ("P2", A(9, 5)), (A(0), A(0))),
    (("N2", A(1)), ("P2", A(0, 3)), (A(0), A(0))),
    (("P1", A(0, 0, 1)), ("P2", A(1, 0, 3)), (A(0), A(-1, 1))),
    (("P1", A(11, 3, 3)), ("P2", A(10, 5, 1)), (A(0), A(-1, 1))),
    (("P1", A(9, 3, 3)), ("P2", A(2, 3, -3)), (A(1), A(-1, 1))),
    (("P1", A(10, 3, 3)), ("P2", A(-3, 3, -3)), (A(0), A(-1, 1))),
    (("P1", A(9, 6)), ("P2", A(2)), (A(0), A(0))),
]

JUNCTION = [("P1", A(0)), ("P1", A(6, 3)), ("P2", A(0)), ("P2", A(4, 3))]
GATE = {"a": "a", "b": "b", "c": "c", "A": "A", "C": "A", "B": "B"}

TEMPLATES = [
    ("T1", [("P1", A(2, 1, 1)), ("P2", A(4, 4, -1))], (A(0), A(-2, 1))),
    ("T2", [("P1", A(1, 2)), ("P2", A(5, 3))], (A(0), A(0))),
    ("T3", [("P1", A(2, 2)), ("P2", A(4, 3))], (A(0), A(0))),
    ("T4", [("P1", A(3, 2)), ("P2", A(3, 3))], (A(0), A(0))),
    ("T5", [("P1", A(4, 2)), ("P2", A(2, 3))], (A(0), A(0))),
    ("T6", [("P1", A(6, 2, 1)), ("P2", A(8, 5, -1))], (A(0), A(-2, 1))),
    ("T7", [("P1", A(5, 3)), ("P2", A(9, 4))], (A(0), A(0))),
    ("T8", [("P1", A(6, 3)), ("P2", A(8, 4))], (A(0), A(0))),
    ("T9", [("P1", A(7, 3)), ("P2", A(7, 4))], (A(0), A(0))),
    ("T10", [("P1", A(8, 3)), ("P2", A(6, 4))], (A(0), A(0))),
    ("T11", [("P1", A(0)), ("P2", A(2))], (A(0), A(0))),
    ("T12", [("P1", A(8, 6)), ("P2", A(0))], (A(0), A(0))),
    ("Q1", [("N1", A(0)), ("P1", A(10, 3)), ("P2", A(-2, 3)), ("P1", A(0, 1))], (A(0), A(0))),
    ("Q2", [("N1", A(1)), ("P1", A(1, 1)), ("P2", A(5, 4)), ("P1", A(9, 3))], (A(0), A(0))),
    ("Q3", [("P1", A(0, 0, 1)), ("P2", A(2, 0, 3)), ("P1", A(10, 6, -3)), ("P2", A(-2, 0, 3))], (A(1), A(-1, 1))),
    ("Q4", [("P1", A(5, 2)), ("P2", A(9, 5)), ("N2", A(1)), ("P2", A(1, 3))], (A(0), A(0))),
    ("Q5", [("P1", A(11, 3, 3)), ("P2", A(11, 5, 1)), ("P1", A(15, 3, 3)), ("P2", A(-3, 3, -3))], (A(0), A(-3, 1))),
    ("Q5'", [("P1", A(5, 6)), ("P2", A(9, 6)), ("P1", A(9, 6)), ("P2", A(3))], (A(0), A(0))),
    ("Q6", [("P1", A(12, 3)), ("P2", A(0, 3)), ("N2", A(0)), ("P2", A(10, 5))], (A(0), A(0))),
]
# templates with a trivial range use no parameter (ci = 0 everywhere)


def in_range(e, lo, hi, reg):
    return nonneg(sub(e, lo), reg) and nonneg(sub(hi, e), reg)


def label(c, e, reg):
    for (cc, s, t, pat) in SEGS:
        if cc != c or not in_range(e, s, t, reg):
            continue
        off = sub(e, s)
        P = len(pat)
        if off[1] % P or off[2] % P or off[0].denominator != 1:
            continue
        return pat[int(off[0]) % P]
    return None


def label_split(c, e, reg, depth=0):
    """set of labels of dart (c, e) over the region; if no single segment covers the region, split
    it into the first parameter value and the rest (used only for image darts)"""
    l = label(c, e, reg)
    if l is not None:
        return {l}
    lo, hi = reg
    assert depth < 3 and hi != lo, ("label undecided", c, e)
    out = set()
    for sub_reg in ((lo, lo), (add(lo, A(1)), hi)):
        try:
            out |= label_split(c, e, sub_reg, depth + 1)
        except ValueError:  # empty at KMIN: handled by the numeric cross-check
            raise
    return out


def p_image(c, e, reg):
    """returns (circle, position) of p(dart) if one rule applies on the whole region"""
    for (x, y, (tlo, thi)) in RULES:
        for (src, dst) in ((x, y), (y, x)):
            if src[0] != c:
                continue
            ps = src[1]
            s = ps[2]
            if s == 0:
                if zero(sub(e, ps), reg):
                    return dst[0], dst[1]
                continue
            # t = (e - ps(t=0)) / s must be integer affine in (k, i)
            num = sub(e, (ps[0], ps[1], Fr(0)))
            t = tuple(v / s for v in num)
            if any(v.denominator != 1 for v in t):
                continue
            if not (nonneg(sub(t, tlo), reg) and nonneg(sub(thi, t), reg)):
                continue
            pd = dst[1]
            img = (pd[0] + pd[2] * t[0], pd[1] + pd[2] * t[1], pd[2] * t[2])
            return dst[0], img
    return None


def nxt(c, e, reg):
    last = sub(LEN[c], A(1))
    if zero(sub(e, last), reg):
        return c, A(0)
    return c, add(e, A(1))


def is_junction(c, e, reg):
    hits = 0
    for (cc, fp) in JUNCTION:
        if cc != c:
            continue
        g = sub(e, fp)
        if zero(g, reg):
            hits += 1
        elif nonneg(sub(g, A(1)), reg) or nonneg(sub(A(-1), g), reg):
            pass
        else:
            return None  # undecided on this region
    return hits


def check(name, darts, reg):
    lo, hi = reg
    labs, junc = [], []
    for t, (c, e) in enumerate(darts):
        img = p_image(c, e, reg)
        assert img is not None, ("no rule applies on the whole region", name, t)
        c2, e2 = nxt(*img, reg)
        cn, en = darts[(t + 1) % len(darts)]
        assert c2 == cn and zero(sub(e2, en), reg), ("sigma step fails", name, t)
        l = label(c, e, reg)
        assert l is not None and label_split(*img, reg) == {l.swapcase()}, ("p does not pair inverse letters", name, t)
        j = is_junction(c, e, reg)
        assert l is not None and j is not None, ("label or junction undecided", name, t)
        labs.append(l); junc.append(j)
    minus = [c[0] == "N" for c, _ in darts]
    assert len({GATE[l] for l in labs}) == len(labs), ("(L)", name, labs)
    assert sum(junc) <= 1, ("(3)", name)
    assert sum(junc) == 0 or len(darts) == 2, ("(2)", name)
    assert sum(minus) <= 1, ("(4) vertex", name)
    say("  %-4s valence %d  labels %s  junction darts %d  minus darts %d  parameter in [%s, %s]" % (
        name, len(darts), "".join(labs), sum(junc), sum(minus), fmt(lo), fmt(hi)))


def fmt(u):
    s = []
    if u[1]:
        s.append("%sk" % ("" if u[1] == 1 else u[1]))
    if u[0] or not s:
        s.append("%+d" % u[0] if s else "%d" % u[0])
    return "".join(s)


say("symbolic check for all k >= %d" % KMIN)
for (x, y, _) in RULES:
    assert not (x[0][0] == "N" and y[0][0] == "N"), "(4) edge"
say("(4) edges: every minus dart is paired with a plus dart")
npairs = A(0)
for (_, _, (tlo, thi)) in RULES:
    npairs = add(npairs, sub(add(thi, A(1)), tlo))
assert npairs == A(12, 6)
say("the rules define 6k+12 pairs; since every dart lies in a rule domain (sigma steps below) and there are 12k+24 darts, the domains are disjoint and p is a well-defined fixed-point-free involution")
size = A(0); verts = A(0)
for name, darts, reg in TEMPLATES:
    check(name, darts, reg)
    cnt = sub(add(reg[1], A(1)), reg[0])  # number of parameter values
    size = add(size, tuple(len(darts) * v for v in cnt))
    verts = add(verts, cnt)
say("size sum", fmt(size), "vertices", fmt(verts))
assert size == A(24, 12) and verts == A(10, 4)
say("chi(X) = V - E = (4k+10) - (6k+12) = -2k-2, genus k+2")

# numeric cross-check: templates equal the orbits for KMIN <= k <= KNUM
spec = importlib.util.spec_from_file_location("fam", os.path.join(os.path.dirname(os.path.abspath(__file__)), "power_two_family_certificates.py"))
sys_argv = sys.argv
sys.argv = [sys.argv[0], "1", "0", os.devnull]
fam = importlib.util.module_from_spec(spec); spec.loader.exec_module(fam)
sys.argv = sys_argv
for k in range(KMIN, KNUM + 1):
    L = 6 * k + 10
    base = {"N1": 0, "P1": 2, "N2": L + 2, "P2": L + 4}
    lab = "bc" + "".join(fam.words(k)[0]) + "CB" + "".join(fam.words(k)[1])
    p = fam.pairing(k)
    ev = lambda u, i: int(u[0] + u[1] * k + u[2] * i)
    listed = set()
    total = 0
    for name, darts, (lo, hi) in TEMPLATES:
        for i in range(ev(lo, 0), ev(hi, 0) + 1):
            o = [base[c] + ev(e, i) for c, e in darts]
            for t, d in enumerate(o):
                nd = o[(t + 1) % len(o)]
                c = next(cc for cc in ("P2", "N2", "P1", "N1") if d >= base[cc])
                q = p[d]
                cq = next(cc for cc in ("P2", "N2", "P1", "N1") if q >= base[cc])
                nq = base[cq] + (q - base[cq] + 1) % (L if cq[0] == "P" else 2)
                assert nq == nd, (k, name, i)
            listed.add(frozenset(o)); total += len(o)
    assert total == len(lab) and len(set().union(*listed)) == len(lab), ("coverage", k)
say("numeric: templates are exactly the vertex orbits and cover all darts for %d <= k <= %d" % (KMIN, KNUM))
say("SYMBOLIC CERTIFICATE OK")
log.close()
