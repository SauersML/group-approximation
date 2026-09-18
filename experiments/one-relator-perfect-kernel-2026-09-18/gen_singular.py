#!/usr/bin/env python3
"""Enumerate two-generator relators w in F(a,t), t-exponent 0, whose Magnus
rewriting has n = NMAX levels, a singular extreme (exponent sum 0, >= 3
syllables) and a UNIT Alexander polynomial (exactly one level with nonzero
exponent sum, equal to +-1), unpeelable at both extremes.  Then run the
landed census certificate search (census.cert_word) and print survivors.
Usage: gen_singular.py LMAX NMAX [BOTH]   (BOTH=1: both extremes singular)"""
import sys, itertools
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/or-unpeelable-census-scripts-2026-09-12')
import census as C
LMAX, NMAX = int(sys.argv[1]), int(sys.argv[2])
BOTH = len(sys.argv) > 3 and sys.argv[3] == '1'
EXPS = [e for e in range(-3, 4) if e]
seen = set(); out = []
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
def length(seq):
    k = len(seq)
    return sum(abs(e) for _, e in seq) + sum(abs(seq[(i+1) % k][0] - seq[i][0]) for i in range(k))
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
    if BOTH and not all(sing): return False
    if not any(sing): return False
    return True
def rec(seq, L):
    if seq and L + abs(seq[-1][0] - seq[0][0]) <= LMAX and len(seq) >= 3 and ok(seq):
        c = canon_seq(seq)
        if c not in seen:
            seen.add(c); out.append(list(c))
    for h in range(NMAX + 1):
        if seq and h == seq[-1][0]: continue
        if not seq and h != 0: continue
        for e in EXPS:
            dl = abs(e) + (abs(h - seq[-1][0]) if seq else 0)
            # lower bound on closing: return to height of seq[0]
            if L + dl + abs(h - 0) > LMAX: continue
            seq.append((h, e)); rec(seq, L + dl); seq.pop()
rec([], 0)
print('candidates', len(out), file=sys.stderr)
for seq in out:
    w = C.cyc_reduce(C.seq_to_word(seq))
    C.BUDGET[0] = 4000
    good, why = C.cert_word(w, 0)
    sums = [sum(e for h, e in seq if h == l) for l in range(NMAX + 1)]
    print('CERT' if good else 'OPEN', C.word_str(w), len(w), 'levels', sums, 'seq', seq, why)
