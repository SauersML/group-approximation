"""Census of two-generator balanced presentations <x, y | r1, r2> with H_1 = 0.

Purpose: the deficiency-zero Kervaire killing-failure filter.  A killing failure over
G = <x, y | r1, r2> needs G != 1 and no nontrivial hyperlinear quotient, in
particular H_1(G) = 0, which for a balanced two-generator presentation is exactly
det [[e_x(r1), e_y(r1)], [e_x(r2), e_y(r2)]] = +-1.

Relators are cyclically reduced words over x, X = x^-1, y, Y = y^-1, of length >= 1.
Classes are taken up to: rotation and inversion of each relator, swapping the two
relators, and the 8 signed permutations of the generators (letter bijections that
respect inverse pairs).  Each of these moves presents an isomorphic group.

Output: one line per class, "<id> <L> <r1> <r2>", L = |r1| + |r2|.
Usage: census_balanced.py LMAX OUT
"""
import sys

INV = {"x": "X", "X": "x", "y": "Y", "Y": "y"}
NEXT = {c: [d for d in "xXyY" if d != INV[c]] for c in "xXyY"}


def inverse(w):
    return "".join(INV[c] for c in reversed(w))


def canon_rel(w):
    best = None
    for v in (w, inverse(w)):
        for i in range(len(v)):
            r = v[i:] + v[:i]
            if best is None or r < best:
                best = r
    return best


def reduced_words(n):
    # freely reduced words of length n, generated letter by letter
    if n == 0:
        return [""]
    stack = [(c,) for c in "xXyY"]
    out = []
    while stack:
        w = stack.pop()
        if len(w) == n:
            out.append("".join(w))
            continue
        for d in NEXT[w[-1]]:
            stack.append(w + (d,))
    return out


def cyclic_classes(n):
    seen = set()
    for w in reduced_words(n):
        if n > 1 and INV[w[0]] == w[-1]:
            continue
        seen.add(canon_rel(w))
    return sorted(seen)


AUTS = [(swap, sx, sy) for swap in (False, True) for sx in (1, -1) for sy in (1, -1)]


def apply_aut(w, aut):
    swap, sx, sy = aut
    img = {"x": ("y" if swap else "x", sx), "y": ("x" if swap else "y", sy)}
    out = []
    for c in w:
        b = c.lower()
        e = -1 if c.isupper() else 1
        g, s = img[b]
        out.append(g if s * e == 1 else g.upper())
    return "".join(out)


def expsum(w):
    return (w.count("x") - w.count("X"), w.count("y") - w.count("Y"))


def canon_pres(r1, r2):
    best = None
    for aut in AUTS:
        a = canon_rel(apply_aut(r1, aut))
        b = canon_rel(apply_aut(r2, aut))
        key = (a, b) if (len(a), a) <= (len(b), b) else (b, a)
        if best is None or (len(key[0]) + len(key[1]), key) < (len(best[0]) + len(best[1]), best):
            best = key
    return best


def main():
    lmax = int(sys.argv[1])
    out = sys.argv[2]
    classes = {n: cyclic_classes(n) for n in range(1, lmax)}
    ex = {n: [(r, expsum(r)) for r in classes[n]] for n in classes}
    found = set()
    counts = {}
    for l1 in range(1, lmax):
        for l2 in range(l1, lmax - l1 + 1):
            for i, (r1, e1) in enumerate(ex[l1]):
                for j, (r2, e2) in enumerate(ex[l2]):
                    if l1 == l2 and j < i:
                        continue
                    if abs(e1[0] * e2[1] - e1[1] * e2[0]) != 1:
                        continue
                    found.add(canon_pres(r1, r2))
    rows = sorted(found, key=lambda p: (len(p[0]) + len(p[1]), p))
    with open(out, "w") as f:
        for k, (a, b) in enumerate(rows):
            L = len(a) + len(b)
            counts[L] = counts.get(L, 0) + 1
            f.write("%d %d %s %s\n" % (k, L, a, b))
    sys.stderr.write("classes per total length: %s\n" % sorted(counts.items()))
    sys.stderr.write("total %d\n" % len(rows))


if __name__ == "__main__":
    main()
