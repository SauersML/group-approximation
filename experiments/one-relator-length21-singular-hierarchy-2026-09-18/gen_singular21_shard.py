#!/usr/bin/env python3
"""Enumerate two-generator relators w in F(a,t), t-exponent 0, whose Magnus
rewriting has n = NMAX levels, a singular extreme (exponent sum 0, >= 3
syllables) and a UNIT Alexander polynomial (exactly one level with nonzero
exponent sum, equal to +-1), unpeelable at both extremes.  Then run the
landed census certificate search (census.cert_word) and print survivors.
Usage: gen_singular21.py LMAX NMAX [BOTH]   (BOTH=1: both extremes singular)
Environment: EMAX (largest |syllable exponent|, default 9), LEXACT (keep only this length).
Copy of experiments/one-relator-perfect-kernel-2026-09-18/gen_singular.py with EMAX and LEXACT added.
Sharded variant: SHARD=i/k restricts the exponent of the first syllable to EXPS[i::k]; PHASE=enum prints
canonical syllable sequences (SEQ lines, dedup across shards with sort -u); PHASE=cert reads SEQ lines
from stdin and runs the certificate search on them.  The closing bound also accounts for a
not-yet-visited top height (exact pruning)."""
import sys, itertools
import os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'research', 'artifacts', 'or-unpeelable-census-scripts-2026-09-12'))
import census as C
LMAX, NMAX = int(sys.argv[1]), int(sys.argv[2])
BOTH = len(sys.argv) > 3 and sys.argv[3] == '1'
EMAX = int(os.environ.get('EMAX', '9'))
LEXACT = os.environ.get('LEXACT')
EXPS = [e for e in range(-EMAX, EMAX + 1) if e]
SHARD = os.environ.get('SHARD')
PHASE = os.environ.get('PHASE', 'enum')
FIRST = EXPS[int(SHARD.split('/')[0])::int(SHARD.split('/')[1])] if SHARD else EXPS
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
def rec(seq, L, mx=0):
    if seq and L + abs(seq[-1][0] - seq[0][0]) <= LMAX and len(seq) >= 3 and \
            (LEXACT is None or L + abs(seq[-1][0] - seq[0][0]) == int(LEXACT)) and ok(seq):
        c = canon_seq(seq)
        if c not in seen:
            seen.add(c); out.append(list(c))
    for h in range(NMAX + 1):
        if seq and h == seq[-1][0]: continue
        if not seq and h != 0: continue
        for e in (FIRST if not seq else EXPS):
            dl = abs(e) + (abs(h - seq[-1][0]) if seq else 0)
            # lower bound on closing: return to height 0 = seq[0][0]; if height NMAX is not yet
            # visited, the rest must climb to NMAX (NMAX - h), spend >= 1 letter there, and come
            # back down (NMAX).  Exact pruning: it discards no sequence that ok() could accept.
            m2 = max(mx, h)
            close = abs(h - 0) if m2 == NMAX else (NMAX - h) + 1 + NMAX
            if L + dl + close > LMAX: continue
            seq.append((h, e)); rec(seq, L + dl, m2); seq.pop()
if PHASE == 'enum':
    rec([], 0)
    print('candidates', len(out), file=sys.stderr)
    for seq in out:
        print('SEQ', repr(seq))
    sys.exit(0)
import ast
out = [ast.literal_eval(l.split(' ', 1)[1]) for l in sys.stdin if l.startswith('SEQ ')]
print('candidates', len(out), file=sys.stderr)
for seq in out:
    w = C.cyc_reduce(C.seq_to_word(seq))
    C.BUDGET[0] = 4000
    good, why = C.cert_word(w, 0)
    sums = [sum(e for h, e in seq if h == l) for l in range(NMAX + 1)]
    print('CERT' if good else 'OPEN', C.word_str(w), len(w), 'levels', sums, 'seq', seq, why, flush=True)
