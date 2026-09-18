"""Calibration for fpbs-dini-singular-boundary-classes-exist-but-one-way-die (free group F_2 = <a,b>).

Letters: a, b, A=a^-1, B=b^-1.  In the Cayley tree (delta = 0) the thin shadow O_s(h) is the cylinder of
rays that share the first max(|h|-s, 0) letters of h.  Lambda_+ = rays using only a, b.

Check 1 (one-way bound, proof Lemma 5): for every s and every y with |y| <= s, any h with
  O_s(h) meets Lambda_+  and  O_s(y h^-1) meets Lambda_+
has |h| <= 4s + 1 (i.e. rho(s) <= 4s + 1).  We enumerate all h up to length HMAX and report the largest such |h|.

Check 2 (Dini divergence, proof Step 2): for the block code with L_n = 4^n the lower bound
  sum_N m_N >= sum_n 2^-n L_n  diverges (partial sums printed).
"""
import itertools

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
POS = set('ab')


def reduce(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def words(n):
    if n == 0:
        yield ''
        return
    for w in words(n - 1):
        for c in 'abAB':
            if not w or w[-1] != INV[c]:
                yield w + c


def meets_pos(h, s):
    k = max(len(h) - s, 0)
    return all(c in POS for c in h[:k])


def check1(HMAX=11, SMAX=3):
    allw = [w for n in range(HMAX + 1) for w in words(n)]
    for s in range(SMAX + 1):
        ys = [w for n in range(s + 1) for w in words(n)]
        best = 0
        for h in allw:
            if not meets_pos(h, s):
                continue
            hi = inv(h)
            if any(meets_pos(reduce(y + hi), s) for y in ys):
                best = max(best, len(h))
        print(f"s={s}: max |h| found = {best}  (bound 4s+1 = {4*s+1}; search depth {HMAX})")
        assert best <= 4 * s + 1


def check2(nmax=12):
    tot = 0
    for n in range(1, nmax + 1):
        tot += 2.0 ** (-n) * 4 ** n
        print(f"n={n}: partial Dini lower sum >= {tot:.0f}")


if __name__ == '__main__':
    check1()
    check2()
