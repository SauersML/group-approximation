#!/usr/bin/env python3
"""Survivor statistics for census.py.

For each length L, rerun the census certifier and, on the uncertified classes,
record: overlap rank R = (n-m)/g, whether some interior letter occurs exactly
once in W_0 (then the Magnus piece B_0 is free), the absolute syllable
exponents at the two extremes, and whether some automorphic image of w
(breadth-first over Whitehead moves, bounded length) is partially positive.
Partial positivity in any basis certifies soficity, since the group is unchanged.
Usage: census2.py L EXTRA CAP
"""
import sys, time
from collections import Counter, deque
import census as C

def ckey(w):
    return min(tuple(w[r:] + w[:r]) for r in range(len(w)))

def pp_search(w, extra, cap):
    w = C.cyc_reduce(w)
    bound = len(w) + extra
    seen = {ckey(w)}
    dq = deque([w])
    while dq:
        v = dq.popleft()
        if C.pp(v):
            return v
        for img in C.WH:
            u = C.subst(v, img)
            if len(u) <= bound:
                k = ckey(u)
                if k not in seen:
                    if len(seen) >= cap:
                        return None
                    seen.add(k)
                    dq.append(u)
    return None

def stats(cs):
    m, n, g, top, bot = C.extremes(cs)
    tot = Counter()
    for h, e in cs:
        tot[h] += abs(e)
    free = any(tot[h] == 1 for h in tot if m < h < n)
    pat = tuple(sorted((tuple(sorted(abs(e) for e in top)),
                        tuple(sorted(abs(e) for e in bot)))))
    return (n - m) // g, g, free, pat

def main():
    L, extra, cap = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    t0 = time.time()
    seen, surv = set(), []
    for seq in C.gen(L):
        m, n, g, top, bot = C.extremes(seq)
        if C.peelable(top) or C.peelable(bot):
            continue
        c = C.canon(seq)
        if c in seen:
            continue
        seen.add(c)
        cs = list(c)
        w = C.seq_to_word(cs)
        if C.min_period(w) < len(w):
            continue
        C.BUDGET[0] = 3000
        ok, why = C.cert_word(w, 0)
        if not ok:
            surv.append((cs, w))
    Rc, Fc, Pc = Counter(), Counter(), Counter()
    b2, ppok, rest = 0, [], []
    for cs, w in surv:
        R, g, free, pat = stats(cs)
        Rc[R] += 1; Fc[free] += 1; Pc[pat] += 1
        if C.expsums(w) == (0, 0):
            b2 += 1
        v = pp_search(w, extra, cap)
        if v is not None:
            ppok.append((w, v))
        else:
            rest.append((cs, w, R, free, pat))
    print('L=%d survivors=%d b1=2:%d R=%s free_piece=%s time=%.0fs'
          % (L, len(surv), b2, sorted(Rc.items()), sorted(Fc.items()), time.time() - t0))
    print(' patterns=%s' % sorted(Pc.items(), key=lambda x: -x[1])[:12])
    print(' pp_bfs(extra=%d,cap=%d) certified=%d remaining=%d' % (extra, cap, len(ppok), len(rest)))
    for w, v in ppok[:5]:
        print('  PPEX %s -> %s' % (C.word_str(w), C.word_str(v)))
    rR, rF = Counter(r[2] for r in rest), Counter(r[3] for r in rest)
    print(' remaining R=%s free_piece=%s' % (sorted(rR.items()), sorted(rF.items())))
    for cs, w, R, free, pat in rest[:8]:
        print('  REST %s seq=%s R=%d free=%s pat=%s' % (C.word_str(w), cs, R, free, pat))
    nonfree = [r for r in rest if not r[3]]
    for cs, w, R, free, pat in nonfree[:5]:
        print('  NONFREE %s seq=%s R=%d pat=%s' % (C.word_str(w), cs, R, pat))
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
