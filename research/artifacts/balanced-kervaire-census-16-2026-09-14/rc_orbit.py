"""Orbit-counting recount of the two-generator balanced census (|det| = 1).

Independent of census_balanced.py (which canonicalizes generated pairs) and of census_check.py
(which enumerates every ordered pair and does not scale past total length 15).  Two exact
computations:

(1) N(l1, l2) = number of ORDERED pairs (a, b) of cyclically reduced words over x, X, y, Y with
    |a| = l1, |b| = l2 and |det [[e_x(a), e_y(a)], [e_x(b), e_y(b)]]| = 1.  It is computed from
    c_n(p, q), the number of cyclically reduced words of length n with exponent sums (p, q), by a
    transfer-matrix count over (first letter, last letter, p, q).  No pair is enumerated.

(2) For each census representative p = (a, b): the move group of its block acts on ordered pairs by
    independent rotations and inversion of the length-l1 word and of the length-l2 word (dihedral
    groups of orders 2 l1 and 2 l2), the 8 signed permutations of {x, y}, and the swap of the two
    positions.  Its order is (2 l1)(2 l2) * 8 * 2 = 64 l1 l2.  Every group element is applied to p
    by brute force, which gives |Stab(p)| and the minimum of the census key over the orbit (the two
    relators sorted by (length, string)).

Checks, per unordered block (l1 <= l2):
  - each representative is cyclically reduced, has |det| = 1 and the stated total length, and
    equals its own orbit minimum, and no representative repeats.  An orbit has one minimum, so
    distinct representatives lie in distinct orbits;
  - 64 l1 l2 / |Stab(p)| is an integer for each p, and these orbit sizes sum to the number of
    ordered pairs in the block's orbit-closed set: 2 N(l1, l2) if l1 != l2, N(l, l) if l1 = l2.
    Orbits partition that set, so the representatives' orbits cover it: one representative per orbit.
Usage: rc_orbit.py CENSUS LMIN LMAX
"""
import sys
from collections import defaultdict

INV = {"x": "X", "X": "x", "y": "Y", "Y": "y"}
DELTA = {"x": (1, 0), "X": (-1, 0), "y": (0, 1), "Y": (0, -1)}
LETTERS = "xXyY"


def inverse(w):
    return "".join(INV[c] for c in reversed(w))


def letter_maps():
    # a signed permutation is fixed by the images of x and of y, taken from different letter pairs
    out = []
    for ix in LETTERS:
        for iy in LETTERS:
            if iy.lower() == ix.lower():
                continue
            out.append(str.maketrans({"x": ix, "X": INV[ix], "y": iy, "Y": INV[iy]}))
    return out


def dihedral(w):
    # images of w under the 2 n elements r^k and r^k o inversion, k = 0 .. n-1
    iw = inverse(w)
    n = len(w)
    return [w[k:] + w[:k] for k in range(n)] + [iw[k:] + iw[:k] for k in range(n)]


def cyc_reduced(w):
    n = len(w)
    if n == 0 or any(c not in INV for c in w):
        return False
    if any(INV[w[i]] == w[i + 1] for i in range(n - 1)):
        return False
    return n == 1 or INV[w[0]] != w[-1]


def expsum(w):
    return (w.count("x") - w.count("X"), w.count("y") - w.count("Y"))


def key(u, v):
    return (u, v) if (len(u), u) <= (len(v), v) else (v, u)


def orbit_data(a, b, maps):
    stab = 0
    best = None
    same = len(a) == len(b)
    for m in maps:
        A = dihedral(a.translate(m))
        B = dihedral(b.translate(m))
        for u in A:
            for v in B:
                if u == a and v == b:
                    stab += 1
                if same and v == a and u == b:
                    stab += 1  # the swapped image (v, u) fixes p
                k = key(u, v)
                if best is None or k < best:
                    best = k
    return stab, best


def word_counts(nmax):
    c = {}
    for n in range(1, nmax + 1):
        cnt = defaultdict(int)
        if n == 1:
            for ch in LETTERS:
                cnt[DELTA[ch]] += 1
        else:
            for f in LETTERS:
                st = defaultdict(int)
                st[(f,) + DELTA[f]] = 1
                for _ in range(n - 1):
                    nst = defaultdict(int)
                    for (last, p, q), k in st.items():
                        for ch in LETTERS:
                            if ch == INV[last]:
                                continue
                            dp, dq = DELTA[ch]
                            nst[(ch, p + dp, q + dq)] += k
                    st = nst
                for (last, p, q), k in st.items():
                    if last != INV[f]:
                        cnt[(p, q)] += k
        c[n] = dict(cnt)
    return c


def ordered_pairs(c, l1, l2):
    tot = 0
    for (p, q), k1 in c[l1].items():
        for (r, s), k2 in c[l2].items():
            if abs(p * s - q * r) == 1:
                tot += k1 * k2
    return tot


def main():
    census, lmin, lmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    maps = letter_maps()
    assert len(maps) == 8
    c = word_counts(lmax)
    orbsum = defaultdict(int)
    nrep = defaultdict(int)
    perL = defaultdict(int)
    seen = set()
    bad = []
    for ln in open(census):
        p = ln.split()
        if len(p) < 4:
            continue
        L = int(p[1])
        if L < lmin or L > lmax:
            continue
        a, b = p[2], p[3]
        l1, l2 = len(a), len(b)
        if l1 + l2 != L:
            bad.append((p[0], "length"))
            continue
        if not (cyc_reduced(a) and cyc_reduced(b)):
            bad.append((p[0], "not-cyclically-reduced"))
            continue
        ea, eb = expsum(a), expsum(b)
        if abs(ea[0] * eb[1] - ea[1] * eb[0]) != 1:
            bad.append((p[0], "det"))
            continue
        if (a, b) in seen:
            bad.append((p[0], "repeat"))
            continue
        seen.add((a, b))
        stab, best = orbit_data(a, b, maps)
        if best != (a, b):
            bad.append((p[0], "not-orbit-minimum"))
            continue
        order = 64 * l1 * l2
        if stab == 0 or order % stab:
            bad.append((p[0], "stabilizer"))
            continue
        blk = (min(l1, l2), max(l1, l2))
        orbsum[blk] += order // stab
        nrep[blk] += 1
        perL[L] += 1
    ok = True
    for L in range(lmin, lmax + 1):
        for l1 in range(1, L // 2 + 1):
            l2 = L - l1
            N = ordered_pairs(c, l1, l2)
            expect = N if l1 == l2 else 2 * N
            got = orbsum[(l1, l2)]
            if got != expect:
                ok = False
            print("block %d %d reps %d orbit_sum %d ordered_pairs %d %s"
                  % (l1, l2, nrep[(l1, l2)], got, expect, "OK" if got == expect else "BAD"))
    print("reps per L:", sorted(perL.items()), "total", sum(perL.values()))
    print("bad representatives:", len(bad), bad[:20])
    print("MATCH" if ok and not bad else "MISMATCH")


if __name__ == "__main__":
    main()
