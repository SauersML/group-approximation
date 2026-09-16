#!/usr/bin/env python3
"""Census of three-generator, two-relator homology-circle presentations.

Search space S_N (exact):  pairs (r1, r2) of cyclically reduced words in the free group on
x1, x2, x3 with |r1| + |r2| <= N and H_1(<x1,x2,x3 | r1, r2>) = Z (Smith form (1,1) of the
2x3 exponent-sum matrix, i.e. the cross product of the exponent rows is primitive).

Mathematical filters (proved in the artifact, not heuristics):
  F0  some generator occurs in neither relator  -> "C0" class, handled by the Kervaire census;
  F1  some generator occurs exactly once in some relator -> Tietze to a two-generator
      one-relator homology circle -> locally indicable (Barreto--Minian Thm 2.9 with k = 0);
  F2  a relator involving a single generator is x^{+-1} (forced by H_1 = Z), so F1 applies.
  F3  a relator in which every generator occurs an even number of times has an even exponent
      row, so every 2x2 minor is even and H_1 != Z.
So the pairs left to test are "admissible": all three generators occur, each relator involves
at least two generators, every generator occurring in a relator occurs there at least twice,
and some generator occurs an odd number of times (hence at least three times).  In particular
every relator has length >= 5.

Symmetry reduction (every pair is isomorphic, as a presentation, to a tested pair):
  r1 runs over representatives of cyclic words of length l1 up to rotation, inversion and the
  48 signed permutations of the generators; r2 runs over all cyclic words of length l2 >= l1 up
  to rotation and inversion.

Certificates (all give local indicability of G = pi_1; with H_2 = 0 this gives asphericity):
  C2  Barreto--Minian Theorem 2.9 with k = 1: for phi = +-phi0 and one relator r, some
      generator occurs exactly once in the multiset of minima m_phi(r);
  C3  Barreto--Minian Corollary 2.12: r attains a unique relative minimum at a generator a,
      and some other generator has phi != 0;
  C6  Barreto--Minian Theorem 2.18 (weakly concatenable relators, k = 2).
Pairs with none of these are written to the residue file.

Usage: census.py N [outprefix [NMIN]]   (tests the totals NMIN <= |r1| + |r2| <= N; default NMIN = 10,
which with the length bound |r_i| >= 5 means every total up to N)
"""
import sys, json, time
from math import gcd
from collections import Counter

GENS = (1, 2, 3)


def inverse(w):
    return tuple(-x for x in reversed(w))


def canon_ri(w):
    """Least rotation of w or of w^-1 (cyclic word up to rotation and inversion)."""
    n = len(w)
    v = inverse(w)
    best = w
    for i in range(n):
        a = w[i:] + w[:i]
        if a < best:
            best = a
        b = v[i:] + v[:i]
        if b < best:
            best = b
    return best


def signed_perms():
    out = []
    perms = [(1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)]
    for p in perms:
        for s1 in (1, -1):
            for s2 in (1, -1):
                for s3 in (1, -1):
                    m = {}
                    for g, img, s in zip(GENS, p, (s1, s2, s3)):
                        m[g] = s * img
                        m[-g] = -s * img
                    out.append(m)
    return out


SP = signed_perms()


def canon_full(w):
    return min(canon_ri(tuple(m[x] for x in w)) for m in SP)


def cyclic_words(l):
    """All cyclically reduced words of length l that are canonical under rotation+inversion."""
    letters = (-3, -2, -1, 1, 2, 3)
    res = []
    w = [0] * l

    def rec(i):
        if i == l:
            if w[-1] == -w[0]:
                return
            t = tuple(w)
            if canon_ri(t) == t:
                res.append(t)
            return
        for x in letters:
            if i > 0 and x == -w[i - 1]:
                continue
            # a canonical word starts with its least letter among w and w^-1
            if i > 0 and (x < w[0] or -x < w[0]):
                continue
            w[i] = x
            rec(i + 1)

    rec(0)
    return res


def admissible(w):
    """F1/F2: at least two generators, each occurring at least twice.  F3: some generator
    occurs an odd number of times (otherwise the exponent row is even and H_1 != Z)."""
    c = Counter(abs(x) for x in w)
    return len(c) >= 2 and min(c.values()) >= 2 and any(v % 2 for v in c.values())


def expvec(w):
    e = [0, 0, 0]
    for x in w:
        e[abs(x) - 1] += 1 if x > 0 else -1
    return tuple(e)


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])


def ivalues(w, phi):
    """I-value of each letter occurrence: the lower endpoint of the traversed 1-cell in the
    infinite cyclic cover (Barreto--Minian Def. 2.14 and Remark 2.15)."""
    p = 0
    out = []
    for x in w:
        d = phi[abs(x) - 1] if x > 0 else -phi[abs(x) - 1]
        q = p + d
        out.append(p if p < q else q)
        p = q
    assert p == 0
    return out


def test_c2(w, phi):
    iv = ivalues(w, phi)
    m = min(iv)
    c = Counter(abs(x) for x, v in zip(w, iv) if v == m)
    for g in GENS:
        if c.get(g, 0) == 1:
            return g
    return None


def test_c3(w, phi):
    iv = ivalues(w, phi)
    for a in GENS:
        vals = [v for x, v in zip(w, iv) if abs(x) == a]
        if not vals:
            continue
        mv = min(vals)
        if vals.count(mv) == 1 and any(phi[c - 1] != 0 for c in GENS if c != a):
            return a
    return None


def weak_info(w, phi):
    """(support of m_phi(w), set of x in m_phi(w) whose normalised +/- counts at the minimum differ)."""
    iv = ivalues(w, phi)
    m = min(iv)
    plus = Counter()
    minus = Counter()
    for x, v in zip(w, iv):
        if v != m:
            continue
        g = abs(x)
        sgn = 1 if x > 0 else -1
        if phi[g - 1] < 0:
            sgn = -sgn
        if sgn > 0:
            plus[g] += 1
        else:
            minus[g] += 1
    supp = set(plus) | set(minus)
    good = {g for g in supp if plus[g] != minus[g]}
    return supp, good


def test_c6(r1, r2, phi):
    s1, g1 = weak_info(r1, phi)
    s2, g2 = weak_info(r2, phi)
    if g1 and (g2 - s1):
        return (1, min(g1), min(g2 - s1))
    if g2 and (g1 - s2):
        return (2, min(g2), min(g1 - s2))
    return None


def certify(r1, r2, phi0):
    for s in (1, -1):
        phi = tuple(s * c for c in phi0)
        for idx, r in ((1, r1), (2, r2)):
            g = test_c2(r, phi)
            if g is not None:
                return ('C2', s, idx, g)
    for s in (1, -1):
        phi = tuple(s * c for c in phi0)
        for idx, r in ((1, r1), (2, r2)):
            g = test_c3(r, phi)
            if g is not None:
                return ('C3', s, idx, g)
    for s in (1, -1):
        phi = tuple(s * c for c in phi0)
        t = test_c6(r1, r2, phi)
        if t is not None:
            return ('C6', s) + t
    return None


def main():
    N = int(sys.argv[1])
    prefix = sys.argv[2] if len(sys.argv) > 2 else 'census_N%d' % N
    NMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 10   # test totals NMIN <= l1 + l2 <= N
    t0 = time.time()
    need = set()
    for l1 in range(5, N // 2 + 1):
        need.add(l1)
        for l2 in range(max(l1, NMIN - l1), N - l1 + 1):
            need.add(l2)
    necks = {}
    for l in sorted(need):
        necks[l] = [w for w in cyclic_words(l) if admissible(w)]
    reps = {}
    for l in range(5, N // 2 + 1):
        reps[l] = sorted({canon_full(w) for w in necks[l]})
    stats = Counter()
    residue = []
    for l1 in sorted(reps):
        for l2 in range(max(l1, NMIN - l1), N - l1 + 1):
            key = '%d+%d' % (l1, l2)
            for r1 in reps[l1]:
                e1 = expvec(r1)
                g1 = {abs(x) for x in r1}
                for r2 in necks[l2]:
                    stats[key + ':pairs'] += 1
                    if len(g1 | {abs(x) for x in r2}) < 3:
                        stats[key + ':C0'] += 1
                        continue
                    c = cross(e1, expvec(r2))
                    if gcd(gcd(c[0], c[1]), c[2]) != 1:
                        continue
                    stats[key + ':H1Z'] += 1
                    cert = certify(r1, r2, c)
                    if cert is None:
                        residue.append((r1, r2, c))
                        stats[key + ':residue'] += 1
                    else:
                        stats[key + ':' + cert[0]] += 1
    out = {
        'N': N,
        'NMIN': NMIN,
        'necklace_counts': {l: len(v) for l, v in necks.items()},
        'rep_counts': {l: len(v) for l, v in reps.items()},
        'stats': dict(sorted(stats.items())),
        'residue_count': len(residue),
        'seconds': round(time.time() - t0, 1),
    }
    with open(prefix + '_summary.json', 'w') as f:
        json.dump(out, f, indent=1)
    with open(prefix + '_residue.txt', 'w') as f:
        for r1, r2, c in residue:
            f.write('%s | %s | phi0=%s\n' % (' '.join(map(str, r1)), ' '.join(map(str, r2)),
                                            ' '.join(map(str, c))))
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
