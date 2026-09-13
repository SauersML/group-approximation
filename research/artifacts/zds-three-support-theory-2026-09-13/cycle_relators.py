#!/usr/bin/env python3
"""Classify cycle relators of Kaplansky graphs for support-3 zero divisors.

supp(alpha) = {1, h2, h3}, letters 0 (identity), 1 (h2), 2 (h3).
A k-cycle carries a 2k-tuple T = [a1,b1,...,ak,bk] with
a_i != b_i and b_i != a_(i+1) (indices mod k), and relator
r(T) = prod_i a_i^-1 b_i (Abdollahi--Taheri, arXiv:1612.00934, Def. of T_C).
Equivalence: rotation by pairs and reversal [b1,a1,bk,ak,...,b2,a2].

Words: lists of nonzero ints, +-1 = h2^{+-1}, +-2 = h3^{+-1}.
"""
import itertools, json, sys
from collections import deque

def red(w):
    out = []
    for c in w:
        if out and out[-1] == -c:
            out.pop()
        else:
            out.append(c)
    return out

def cred(w):
    w = red(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w

def inv(w):
    return [-c for c in reversed(w)]

def relator(T):
    k = len(T) // 2
    w = []
    for i in range(k):
        a, b = T[2 * i], T[2 * i + 1]
        if a:
            w.append(-a)
        if b:
            w.append(b)
    return cred(w)

def tuples(k):
    for T in itertools.product((0, 1, 2), repeat=2 * k):
        if all(T[j] != T[(j + 1) % (2 * k)] for j in range(2 * k)):
            yield T

def tuple_class(T):
    k = len(T) // 2
    cands = []
    pairs = [(T[2 * i], T[2 * i + 1]) for i in range(k)]
    for s in range(k):
        rot = pairs[s:] + pairs[:s]
        cands.append(tuple(x for p in rot for x in p))
    # reversal: [b1,a1,bk,ak,...,b2,a2]
    revp = [(pairs[0][1], pairs[0][0])] + [(pairs[i][1], pairs[i][0]) for i in range(k - 1, 0, -1)]
    for s in range(k):
        rot = revp[s:] + revp[:s]
        cands.append(tuple(x for p in rot for x in p))
    return min(cands)

# signed letter permutations of F(h2,h3)
SYMS = []
for perm in ((1, 2), (2, 1)):
    for s1 in (1, -1):
        for s2 in (1, -1):
            SYMS.append({1: perm[0] * s1, 2: perm[1] * s2})

def apply_sym(w, m):
    return [m[abs(c)] * (1 if c > 0 else -1) for c in w]

def canon(w):
    """Canonical cyclic word up to rotation, inversion and signed letter permutation."""
    w = cred(w)
    if not w:
        return ()
    best = None
    for m in SYMS:
        for u in (apply_sym(w, m), inv(apply_sym(w, m))):
            n = len(u)
            for s in range(n):
                t = tuple(u[s:] + u[:s])
                if best is None or t < best:
                    best = t
    return best

# elementary Nielsen automorphisms: images of generators 1 and 2
NIELSEN = []
for (g, h) in ((1, 2), (2, 1)):
    for e in (1, -1):
        NIELSEN.append({g: [g, h * e], h: [h]})
        NIELSEN.append({g: [h * e, g], h: [h]})
        # Whitehead moves of conjugation type
        NIELSEN.append({g: [h * e, g, -h * e], h: [h]})

def apply_aut(w, phi):
    out = []
    for c in w:
        img = phi[abs(c)]
        out.extend(img if c > 0 else inv(img))
    return cred(out)

def minimal_forms(w, slack=4, maxnodes=60000):
    w0 = canon(w)
    seen = {w0}
    q = deque([w0])
    best = len(w0)
    bound = len(w0) + slack
    while q and len(seen) < maxnodes:
        u = q.popleft()
        for phi in NIELSEN:
            v = canon(apply_aut(list(u), phi))
            if len(v) <= bound and v not in seen:
                seen.add(v)
                q.append(v)
                best = min(best, len(v))
    return best, sorted(x for x in seen if len(x) == best)

def syllables(w):
    syl = []
    for c in w:
        if syl and syl[-1][0] == abs(c) and (syl[-1][1] > 0) == (c > 0):
            syl[-1][1] += 1 if c > 0 else -1
        else:
            syl.append([abs(c), 1 if c > 0 else -1])
    if len(syl) >= 2 and syl[0][0] == syl[-1][0] and (syl[0][1] > 0) == (syl[-1][1] > 0):
        syl[0][1] += syl[-1][1]
        syl.pop()
    return syl

def proper_power(w):
    n = len(w)
    for d in range(1, n):
        if n % d == 0 and n // d >= 2 and w == w[:d] * (n // d):
            return list(w[:d]), n // d
    return None

def classify(w, depth=0):
    """Return (type, detail). Types:
    free: freely trivial; A: forces H cyclic or abelian; T: forces a
    generator torsion; S: H is a quotient of a solvable group (BS(1,k),
    Klein bottle); C: torus-type u^a = v^b, |a|,|b| >= 2, not (2,2);
    B: BS(m,n) with |m|,|n| >= 2; G: none of these."""
    w = cred(w)
    if not w:
        return ("free", "")
    m, forms = minimal_forms(w)
    for f in forms:
        pp = proper_power(list(f))
        if pp:
            base, k = pp
            t, d = classify(base, depth + 1)
            return (t, "power^%d of %s:%s" % (k, t, d))
    types = []
    for f in forms:
        syl = syllables(list(f))
        if len(syl) == 1:
            types.append(("A", "primitive power %s" % (f,)))
        elif len(syl) == 2:
            a, b = abs(syl[0][1]), abs(syl[1][1])
            if a == 1 or b == 1:
                types.append(("A", "primitive %s" % (f,)))
            elif a == 2 and b == 2:
                types.append(("S", "Klein u^2=v^+-2 %s" % (f,)))
            else:
                types.append(("C", "torus u^%d v^%d" % (syl[0][1], syl[1][1])))
        elif len(syl) == 4:
            (g1, e1), (g2, e2), (g3, e3), (g4, e4) = syl
            for rot in range(4):
                S = syl[rot:] + syl[:rot]
                (p, e1), (q, e2), (p2, e3), (q2, e4) = S
                if p == p2 and q == q2 and abs(e1) == 1 and e3 == -e1:
                    mm, nn = e2, -e4
                    if abs(mm) == 1 or abs(nn) == 1:
                        types.append(("S", "BS(%d,%d)" % (mm, nn)))
                    else:
                        types.append(("B", "BS(%d,%d)" % (mm, nn)))
                    break
    order = {"A": 0, "T": 1, "S": 2, "C": 3, "B": 4}
    if types:
        return min(types, key=lambda t: order[t[0]])
    return ("G", "min length %d: %s" % (m, " | ".join(str(f) for f in forms[:4])))

def run(k):
    classes = {}
    count = 0
    for T in tuples(k):
        count += 1
        c = tuple_class(T)
        classes.setdefault(c, T)
    res = []
    for c in sorted(classes):
        r = relator(list(c))
        t, d = classify(r)
        res.append({"tuple": list(c), "relator": r, "type": t, "detail": d})
    summ = {}
    for x in res:
        summ[x["type"]] = summ.get(x["type"], 0) + 1
    return count, len(classes), summ, res

if __name__ == "__main__":
    ks = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    out = {}
    for k in ks:
        count, ncl, summ, res = run(k)
        out[k] = {"tuples": count, "classes": ncl, "summary": summ, "classes_detail": res}
        print("k=%d tuples=%d classes=%d summary=%s" % (k, count, ncl, summ))
        for x in res:
            if x["type"] in ("C", "B", "G", "free"):
                print("  ", x["type"], x["tuple"], x["relator"], x["detail"])
    json.dump(out, open("cycle_relators.json", "w"), indent=1)
