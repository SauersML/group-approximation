"""Independent recount of the two-generator balanced census (det = +-1), for total length <= LMAX.

Differs from census_balanced.py in method: it enumerates EVERY ordered pair of cyclically reduced
words (no representative choice up front), and computes each pair's class as the minimum over
its full orbit under the move group, found by breadth-first closure under the generating moves
(rotate r1, rotate r2, invert r1, invert r2, swap, and the three signed generator moves
x -> X, y -> Y, x <-> y).  The orbit minimum uses the same ordering key as the census
(total length, then the sorted pair).  It then compares the per-length class counts, and the
exact set of classes, with the census file.
Usage: census_check.py CENSUS LMAX
"""
import sys
from itertools import product

INV = {"x": "X", "X": "x", "y": "Y", "Y": "y"}


def cyc_reduced_words(n):
    out = []
    for w in product("xXyY", repeat=n):
        ok = all(INV[w[i]] != w[i + 1] for i in range(n - 1))
        if ok and (n == 1 or INV[w[0]] != w[-1]):
            out.append("".join(w))
    return out


def inverse(w):
    return "".join(INV[c] for c in reversed(w))


def moves(p):
    a, b = p
    yield (a[1:] + a[:1], b)
    yield (a, b[1:] + b[:1])
    yield (inverse(a), b)
    yield (a, inverse(b))
    yield (b, a)
    yield (a.translate(str.maketrans("xX", "Xx")), b.translate(str.maketrans("xX", "Xx")))
    yield (a.translate(str.maketrans("yY", "Yy")), b.translate(str.maketrans("yY", "Yy")))
    yield (a.translate(str.maketrans("xXyY", "yYxX")), b.translate(str.maketrans("xXyY", "yYxX")))


def key(p):
    a, b = p
    lo, hi = sorted([a, b], key=lambda s: (len(s), s))
    return (len(a) + len(b), lo, hi)


def orbit_min(p, memo):
    if p in memo:
        return memo[p]
    seen = {p}
    stack = [p]
    while stack:
        q = stack.pop()
        for r in moves(q):
            if r not in seen:
                seen.add(r)
                stack.append(r)
    m = min(key(q) for q in seen)
    for q in seen:
        memo[q] = m
    return m


def det(a, b):
    ex = lambda w: (w.count("x") - w.count("X"), w.count("y") - w.count("Y"))
    (p, q), (r, s) = ex(a), ex(b)
    return p * s - q * r


def main():
    census, lmax = sys.argv[1], int(sys.argv[2])
    words = {n: cyc_reduced_words(n) for n in range(1, lmax)}
    memo = {}
    classes = set()
    for l1 in range(1, lmax):
        for l2 in range(1, lmax - l1 + 1):
            for a in words[l1]:
                for b in words[l2]:
                    if abs(det(a, b)) != 1:
                        continue
                    classes.add(orbit_min((a, b), memo))
    counts = {}
    for c in classes:
        counts[c[0]] = counts.get(c[0], 0) + 1
    print("recount per L:", sorted(counts.items()), "total", len(classes))
    cen = set()
    for ln in open(census):
        p = ln.split()
        if int(p[1]) <= lmax:
            lo, hi = sorted([p[2], p[3]], key=lambda s: (len(s), s))
            cen.add((int(p[1]), lo, hi))
    # census representatives must lie in distinct recount classes, one per class
    reps = {}
    for c in cen:
        m = orbit_min((c[1], c[2]), memo)
        reps.setdefault(m, []).append(c)
    dup = [m for m, v in reps.items() if len(v) > 1]
    missing = classes - set(reps)
    extra = set(reps) - classes
    print("census classes", len(cen), "duplicates", len(dup), "missing", len(missing), "extra", len(extra))
    print("MATCH" if not dup and not missing and not extra and len(cen) == len(classes) else "MISMATCH")


if __name__ == "__main__":
    main()
