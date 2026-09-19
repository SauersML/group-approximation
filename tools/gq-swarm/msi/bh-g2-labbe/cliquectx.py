#!/usr/bin/env python3
"""cliquectx.py -- contextual closure with clique contexts ("stacked contexts"), lane bh-g2-labbe, 2026-09-18.

Sound criterion (node contextual-closure-certifies-quantum-rigidity, item 2) with T, T', S arbitrary finite sets:
T ∋ 0 and T' ∋ v commuting (all pairwise offsets certified), S ⊆ T ∩ T'.  Patterns on T are admissible: for every
5 x 5 box B meeting T, the restriction to T ∩ B extends to a legal box pattern.  If no S-pattern extendable to both
T and T' leaves both ends undetermined, [P_0, P_v] = 0 in the scale-2 presentation of Labbe's shift.
Starts from the certified set of the rectangular closure (radius 4 plus 26 offsets at distance 5).
Usage: python3 cliquectx.py [--smoke]
"""
import sys, time
from collections import defaultdict
import j2probe as J

def log(*a): print('[%7.1fs]' % J.el(), *a, flush=True)
SMOKE = "--smoke" in sys.argv
MARG = 3 if SMOKE else 4
if not SMOKE: J.BUDGET = 1600
LAB5 = sorted(J.labbe_windows(5, 5))
MC = {}
def proj(mask):
    r = MC.get(mask)
    if r is None:
        r = set(tuple(P[i][j] for (i, j) in mask) for P in LAB5); MC[mask] = r
    return r

def admissible(sites, cap):
    order = sorted(sites); pos = {z: k for k, z in enumerate(order)}
    xs = [z[0] for z in order]; ys = [z[1] for z in order]
    checks = defaultdict(list)
    for bx in range(min(xs) - 4, max(xs) + 1):
        for by in range(min(ys) - 4, max(ys) + 1):
            ins = sorted((pos[z], (z[0] - bx, z[1] - by)) for z in order if bx <= z[0] <= bx + 4 and by <= z[1] <= by + 4)
            if ins: checks[ins[-1][0]].append((tuple(i for i, _ in ins), tuple(m for _, m in ins)))
    left = [pos.get((z[0] - 1, z[1])) for z in order]; below = [pos.get((z[0], z[1] - 1)) for z in order]
    pats = [()]
    for k in range(len(order)):
        new = []; L_, B_ = left[k], below[k]
        for p in pats:
            for a in range(19):
                if L_ is not None and J.RT[p[L_]] != J.LF[a]: continue
                if B_ is not None and J.TP[p[B_]] != J.BT[a]: continue
                q = p + (a,)
                if all(tuple(q[i] for i in idx) in proj(mask) for idx, mask in checks[k]): new.append(q)
        pats = new
        if len(pats) > cap: return order, None
    return order, pats

def main():
    unc5 = [(-5, -5), (-5, -4), (-5, 4), (-5, 5), (-4, -5), (-4, 5), (-3, 5), (3, -5), (4, -5), (4, 5), (5, -5), (5, -4), (5, 4), (5, 5)]
    C = set((a, b) for a in range(-5, 6) for b in range(-5, 6)) - set(unc5)
    det_ok = J.rule_tester(set(LAB5), 5)
    cap = 20000 if SMOKE else 200000
    Tmax = 30 if SMOKE else 48
    Rstop = 6 if SMOKE else 8
    tried = {}
    def comm(z, w): return (z[0] - w[0], z[1] - w[1]) in C
    def greedy(seed, cands, key, limit):
        out = list(seed)
        for z in sorted(cands, key=key):
            if len(out) >= limit: break
            if z not in out and all(comm(z, w) for w in out): out.append(z)
        return out
    def certify(v):
        R = max(abs(v[0]), abs(v[1])) + 3
        box = [(x, y) for x in range(min(0, v[0]) - MARG, max(0, v[0]) + MARG + 1) for y in range(min(0, v[1]) - MARG, max(0, v[1]) + MARG + 1)]
        both = [z for z in box if z not in ((0, 0), v) and comm(z, (0, 0)) and comm(z, v)]
        mid = ((v[0]) / 2.0, (v[1]) / 2.0)
        n0 = lambda z: max(abs(z[0]), abs(z[1])); nv = lambda z: max(abs(z[0] - v[0]), abs(z[1] - v[1]))
        variants = [('mid', lambda z: (max(n0(z), nv(z)), z)), ('near0', lambda z: (n0(z), nv(z), z)),
                    ('nearv', lambda z: (nv(z), n0(z), z)), ('far', lambda z: (-min(n0(z), nv(z)), z))]
        for name, key in variants:
            S = greedy([], both, key, 26)
            if not S: continue
            T = greedy([(0, 0)] + S, [z for z in box if comm(z, (0, 0))], lambda z: (n0(z), z), Tmax)
            Tp = greedy([v] + S, [z for z in box if comm(z, v)], lambda z: (nv(z), z), Tmax)
            if len(set(T) - set(S)) < 1: continue
            o0, P0 = admissible(T, cap); o1, P1 = admissible(Tp, cap)
            if P0 is None or P1 is None: continue
            Ss = sorted(S)
            i0 = o0.index((0, 0)); iv = o1.index(v)
            s0 = [o0.index(z) for z in Ss]; s1 = [o1.index(z) for z in Ss]
            d0 = {}; d1 = {}
            for p in P0:
                t = tuple(p[i] for i in s0); o = d0.get(t)
                d0[t] = p[i0] if o is None else (o if o == p[i0] else -1)
            for p in P1:
                t = tuple(p[i] for i in s1); o = d1.get(t)
                d1[t] = p[iv] if o is None else (o if o == p[iv] else -1)
            bad = sum(1 for t, a in d0.items() if a == -1 and d1.get(t) == -1)
            tried[v] = (name, len(S), len(T), len(Tp), len(P0), len(P1), bad)
            if bad == 0: return (name, len(S), len(T), len(Tp), len(P0), len(P1))
        return None
    pending = list(unc5)
    for r in range(5, Rstop + 1):
        if r > 5: pending += [(a, b) for a in range(-r, r + 1) for b in range(-r, r + 1) if max(abs(a), abs(b)) == r]
        progress = True; nd = nc = 0
        while progress and pending and J.el() < J.BUDGET:
            progress = False; rest = []
            for v in pending:
                if v in C: continue
                if det_ok(v, C):
                    C.add(v); C.add((-v[0], -v[1])); nd += 1; progress = True; log('  CERT det', v); continue
                w = certify(v)
                if w:
                    C.add(v); C.add((-v[0], -v[1])); nc += 1; progress = True; log('  CERT clique', v, w)
                else: rest.append(v)
            pending = [v for v in rest if v not in C]
        unc = sorted(set(v for v in pending if v not in C))
        log('CLIQUE ring %d: +det %d +clique %d; uncertified within ring %d: %d %s' % (r, nd, nc, r, len(unc), unc[:24]))
        for v in unc[:10]:
            if v in tried: log('   best try', v, 'variant/|S|/|T|/|T\'|/#T/#T\'/double-open contexts =', tried[v])
        if J.el() > J.BUDGET: log('time budget'); break
    log('DONE')

if __name__ == '__main__':
    main()
