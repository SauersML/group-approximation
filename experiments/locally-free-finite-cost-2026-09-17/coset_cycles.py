"""Simple cycles in the coset graph of H = <a, b a b^-2> in F(a, b), t = b.

Sanity check for research/fpbs-malnormal-coset-cycles-bounded-syllables.md:
for k b-edges the syllables obey |h_i| <= (k-1)(D-1) + k with D = m^2 = 9, and
the number of cycles stabilizes as the syllable search radius L grows.
Letters a, b; inverses A, B.
"""
import itertools
import sys

INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
# Folded based Stallings graph of H (m = 3): a:0->0, b:0->1, a:1->2, b:1->2.
EDGES = {(0, "a"): 0, (0, "b"): 1, (1, "a"): 2, (1, "b"): 2}
REV = {(v, INV[x]): u for (u, x), v in EDGES.items()}
STEP = {**EDGES, **REV}


def red(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return "".join(out)


def inv(w):
    return "".join(INV[x] for x in reversed(w))


def in_H(w):
    v = 0
    for x in w:
        v = STEP.get((v, x))
        if v is None:
            return False
    return v == 0


def H_elements(L):
    gens = ["a", "A", red("baBB"), red(inv("baBB"))]
    seen = {""}
    frontier = {""}
    for _ in range(L):
        new = set()
        for w in frontier:
            for g in gens:
                u = red(w + g)
                if u not in seen:
                    seen.add(u)
                    new.add(u)
        frontier = new
    return sorted(seen, key=len)


def cycles(k, L):
    Hs = H_elements(L)
    found = set()
    for eps in itertools.product("bB", repeat=k):
        for hs in itertools.product(Hs, repeat=k - 1):
            tail = eps[0] + "".join(h + e for h, e in zip(hs, eps[1:]))
            h0 = red(inv(tail))
            if not in_H(h0):
                continue
            syl = (h0,) + hs
            pref, prefs = "", []
            for h, e in zip(syl, eps):
                prefs.append(pref)
                pref = red(pref + h + e)
            assert pref == ""
            if all(not in_H(red(inv(prefs[i]) + prefs[j]))
                   for i in range(k) for j in range(i + 1, k)):
                found.add((eps, syl))
    return found


if __name__ == "__main__":
    for k, L in [(2, 6), (3, 3), (3, 4)]:
        f = cycles(k, L)
        mx = max((max(len(h) for h in s) for _, s in f), default=0)
        print(f"k={k} L={L} cycles={len(f)} max|h|={mx} bound={(k-1)*8+k}")
        sys.stdout.flush()
