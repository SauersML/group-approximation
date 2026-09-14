"""Unimodular one-variable words over G = <x, y | r1, r2> for the collapse test.

Words are cyclic syllable sequences g_0 t^(e_0) g_1 t^(e_1) ... g_(n-1) t^(e_(n-1)), e_i = +-1,
sum e_i = +1, coefficients g_i in COEFFS (freely reduced words over x X y Y, "1" = empty),
with g_i != 1 at opposite-sign corners (cyclic reduction in G * <t> at the free level).
Canonical representative: minimum over rotations; sigma(w^-1) is not used here because
t -> t^-1 flips the degree to -1 and is covered by the degree-(+1) enumeration of w^-1's rotations.
n = 1 is omitted: w = g t gives G_w = G.
Output: "<id> <r1> <r2> <word>" for every survivor line "<gid> <L> <r1> <r2> OPEN ...".
Usage: gen_words.py SURVIVORS OUT NMAX COEFF_LEN
"""
import sys
from itertools import product

INV = {"x": "X", "X": "x", "y": "Y", "Y": "y"}


def reduced(maxlen):
    out = [""]
    frontier = [""]
    for _ in range(maxlen):
        nxt = []
        for w in frontier:
            for c in "xXyY":
                if w and INV[w[-1]] == c:
                    continue
                nxt.append(w + c)
        out.extend(nxt)
        frontier = nxt
    return out


def word_string(signs, coeffs):
    return "".join(g + ("t" if e > 0 else "T") for g, e in zip(coeffs, signs))


def canonical(signs, coeffs):
    n = len(signs)
    return min(word_string(signs[i:] + signs[:i], coeffs[i:] + coeffs[:i]) for i in range(n))


def words(nmax, clen):
    coeffs = reduced(clen)
    seen = set()
    for n in range(3, nmax + 1, 2):
        for signs in product((1, -1), repeat=n):
            if sum(signs) != 1:
                continue
            for cs in product(coeffs, repeat=n):
                ok = True
                for i in range(n):
                    if signs[i - 1] != signs[i] and cs[i] == "":
                        ok = False
                        break
                if ok:
                    seen.add(canonical(list(signs), list(cs)))
    return sorted(seen, key=lambda s: (len(s), s))


def main():
    surv, out, nmax, clen = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    ws = words(nmax, clen)
    k = 0
    with open(surv) as f, open(out, "w") as g:
        for ln in f:
            p = ln.split()
            if len(p) < 5 or p[4] != "OPEN":
                continue
            for w in ws:
                g.write("%s.%d %s %s %s\n" % (p[0], k, p[2], p[3], w))
                k += 1
    sys.stderr.write("words per group %d, lines %d\n" % (len(ws), k))


if __name__ == "__main__":
    main()
