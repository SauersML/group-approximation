import sys
sys.path.insert(0, '../amalgam-segment-steps-2026-09-17')
import frontier_check as fc
hc = fc.hc

def rewrites(s):
    """All span-2 Magnus rewrites (r', e, occ) of the word, over both zero-exponent letters."""
    w = hc.canon(hc.cred(fc.P(s)))
    if 0 not in hc.exps(w).values():
        w = hc.nielsen_zero(w)
    e = hc.exps(w)
    out = []
    for t in [a for a in e if e[a] == 0]:
        r = hc.rewrite(w, t)
        lo = min(p for (_, p), _ in r)
        r = tuple(((0, p - lo), x) for (_, p), x in r)
        m = max(p for (_, p), _ in r)
        ev = [0] * (m + 1); occ = [0] * (m + 1)
        for (_, p), x in r:
            ev[p] += x; occ[p] += 1
        out.append((r, ev, occ))
    return out

if __name__ == '__main__':
    from collections import Counter
    C = Counter()
    for s in open(sys.argv[1]).read().split():
        for r, ev, occ in rewrites(s):
            C[(tuple(occ), tuple(ev))] += 1
            if len(sys.argv) > 2:
                print(s, fc.sc.show(r), ev, occ)
    for k, v in sorted(C.items()):
        print(k, v)
