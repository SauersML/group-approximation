#!/usr/bin/env python3
"""Structured enumerator for the same census as gen_singular21.py (exact length LEN, NMAX levels),
much faster for NMAX >= 3.  A candidate is a cyclic syllable sequence ((h_1,e_1),...,(h_k,e_k)):
syllable a^(e_i) at height h_i, consecutive heights distinct (cyclically), min height 0, max NMAX,
length sum|e_i| + sum|h_(i+1)-h_i| = LEN.
Step 1: height walks h_1 = 0, ..., h_k (some syllable is at height 0, so rotating to it loses
nothing), with k + T <= LEN where T is the cyclic t-cost (each syllable costs >= 1).
Step 2: exponents: B = LEN - T is split among the levels, and at each level the syllables get
nonzero exponents with sum 0, except at one level where the sum is +-1 (unit Alexander
polynomial).  Every sequence is then filtered by ok() and canonicalised by canon_seq(), both
copied verbatim from gen_singular21.py, so the output set is the same as gen_singular21.py's.
Output: SEQ lines, for PHASE=cert of gen_singular21_shard.py.
Usage: gen_walk21.py LEN NMAX"""
import sys, os
from functools import lru_cache
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'research', 'artifacts', 'or-unpeelable-census-scripts-2026-09-12'))
import census as C
LEN, NMAX = int(sys.argv[1]), int(sys.argv[2])


def canon_seq(seq):
    best = None
    k = len(seq)
    for s in (seq, [(NMAX - h, e) for h, e in seq]):
        for v in (s, [(h, -e) for h, e in reversed(s)]):
            for sgn in (1, -1):
                vv = [(h, sgn * e) for h, e in v]
                for r in range(k):
                    u = tuple(vv[r:] + vv[:r])
                    if best is None or u < best: best = u
    return best


def ok(seq):
    k = len(seq)
    if any(seq[i][0] == seq[(i+1) % k][0] for i in range(k)): return False
    hs = [h for h, _ in seq]
    if min(hs) != 0 or max(hs) != NMAX: return False
    sums = [sum(e for h, e in seq if h == l) for l in range(NMAX + 1)]
    nz = [x for x in sums if x]
    if not (len(nz) == 1 and abs(nz[0]) == 1): return False
    top = [e for h, e in seq if h == NMAX]; bot = [e for h, e in seq if h == 0]
    if C.peelable(top) or C.peelable(bot): return False
    sing = [sums[0] == 0, sums[NMAX] == 0]
    if not any(sing): return False
    return True


@lru_cache(maxsize=None)
def tuples(c, b, s):
    """all c-tuples of nonzero ints with sum of |.| = b and sum = s"""
    if c == 0:
        return [()] if (b == 0 and s == 0) else []
    out = []
    for a in range(1, b - (c - 1) + 1):
        for e in (a, -a):
            for rest in tuples(c - 1, b - a, s - e):
                out.append((e,) + rest)
    return out


def walks():
    """height sequences starting at 0, consecutive distinct, cyclic, covering 0..NMAX"""
    res = []
    def rec(hs, T):
        k = len(hs)
        # close the cycle
        if k >= 3 or (k >= 2):
            last = hs[-1]
            if last != hs[0]:
                Tc = T + abs(last - hs[0])
                if k + Tc <= LEN and min(hs) == 0 and max(hs) == NMAX:
                    res.append((tuple(hs), Tc))
        for h in range(NMAX + 1):
            if h == hs[-1]: continue
            T2 = T + abs(h - hs[-1])
            mx = max(max(hs), h)
            close = h if mx == NMAX else (NMAX - h) + NMAX   # t-cost still needed to close
            if (k + 1) + T2 + close > LEN: continue
            hs.append(h); rec(hs, T2); hs.pop()
    rec([0], 0)
    return res


def main():
    seen = set()
    nw = 0
    for hs, T in walks():
        k = len(hs)
        B = LEN - T
        if B < k: continue
        nw += 1
        levels = [[i for i in range(k) if hs[i] == l] for l in range(NMAX + 1)]
        cnt = [len(x) for x in levels]
        # distribute B over levels (b_l >= cnt_l), choose the unit level u and its sign
        def dist(l, rem, acc):
            if l == NMAX:
                yield acc + [rem]
                return
            rest_min = sum(cnt[l + 1:])
            for b in range(cnt[l], rem - rest_min + 1):
                yield from dist(l + 1, rem - b, acc + [b])
        for bl in dist(0, B, []):
            if bl[-1] < cnt[-1]: continue
            for u in range(NMAX + 1):
                for sg in (1, -1):
                    opts = [tuples(cnt[l], bl[l], sg if l == u else 0) for l in range(NMAX + 1)]
                    if any(not o for o in opts): continue
                    def build(l, e):
                        if l > NMAX:
                            seq = [(hs[i], e[i]) for i in range(k)]
                            if len(seq) >= 3 and ok(seq):
                                c = canon_seq(seq)
                                if c not in seen:
                                    seen.add(c)
                            return
                        for t in opts[l]:
                            e2 = list(e)
                            for i, x in zip(levels[l], t): e2[i] = x
                            build(l + 1, e2)
                    build(0, [0] * k)
    print('walks', nw, 'candidates', len(seen), file=sys.stderr)
    for c in sorted(seen):
        print('SEQ', repr(list(c)))


main()
