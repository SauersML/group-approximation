#!/usr/bin/env python3
"""Checks for tall-cylinder-seams-reglue-within-quadratic-profile.

A surface is a list of horizontal cylinders (width w_j, height h_j) plus a seam bijection
sigma: top points -> bottom points.  Squares are (j, y, x); b = right, c = up.
For each random surface we compute
  rho_hat = max_{1<=s<=S, 1<=t<=T} rank([b^s, c^t] - I)/(s+t)   (a lower bound for rho),
  opt     = exact minimal #points where c' != c over commuting c' with b' = b (assignment),
  alg     = cost of the majority-class regluing of the proof,
and assert: m <= 4 rho_hat, every lemma inequality at the tested (s,t) (width, offset, height gap), and
  opt <= alg <= rho_hat^2 (96 + 80 W/H).
Usage: seams.py [trials] [seed]
"""
import random, sys
import numpy as np
from scipy.optimize import linear_sum_assignment

def build(ws, hs, sig):
    idx = {}
    for j, (w, h) in enumerate(zip(ws, hs)):
        for y in range(h):
            for x in range(w):
                idx[(j, y, x)] = len(idx)
    d = len(idx); b = [0]*d; c = [0]*d
    for (j, y, x), i in idx.items():
        b[i] = idx[(j, y, (x+1) % ws[j])]
        c[i] = idx[(j, y+1, x)] if y < hs[j]-1 else idx[(sig[(j, x)][0], 0, sig[(j, x)][1])]
    return idx, b, c

def comp(p, q): return [p[q[i]] for i in range(len(q))]      # p o q
def inv(p):
    r = [0]*len(p)
    for i, v in enumerate(p): r[v] = i
    return r
def power(p, k):
    r = list(range(len(p))); base = p if k >= 0 else inv(p); k = abs(k)
    while k:
        if k & 1: r = comp(base, r)
        base = comp(base, base); k >>= 1
    return r
def ncyc(p):
    seen = [False]*len(p); n = 0
    for i in range(len(p)):
        if not seen[i]:
            n += 1; j = i
            while not seen[j]: seen[j] = True; j = p[j]
    return n
def comm_rank(b, c, s, t):
    bs, ct = power(b, s), power(c, t)
    P = comp(comp(bs, ct), comp(inv(bs), inv(ct)))
    return len(P) - ncyc(P)
def N(b, c, s, t):   # #{y : c^t b^s y != b^s c^t y}
    bs, ct = power(b, s), power(c, t)
    return sum(1 for y in range(len(b)) if ct[bs[y]] != bs[ct[y]])

def random_seam(ws, rng, k):
    """Piecewise-translation seam with about k pieces between the tops and the bottoms."""
    tops = []; bots = []
    for j in rng.sample(range(len(ws)), len(ws)):
        o = rng.randrange(ws[j]); tops += [(j, (o+x) % ws[j]) for x in range(ws[j])]
    for j in rng.sample(range(len(ws)), len(ws)):
        o = rng.randrange(ws[j]); bots += [(j, (o+x) % ws[j]) for x in range(ws[j])]
    L = len(tops); cuts = sorted(rng.sample(range(1, L), min(k-1, L-1))) if L > 1 else []
    pieces = [tops[a:bb] for a, bb in zip([0]+cuts, cuts+[L])]
    rng.shuffle(pieces); line = [p for pc in pieces for p in pc]
    return {line[i]: bots[i] for i in range(L)}

def opt_cost(ws, hs, idx, b, c):
    """Exact min #changed points of c over c' commuting with b (b fixed): rows must map to
    equal-length rows by a rotation; min-cost matching per length class."""
    rows = [(j, y) for j in range(len(ws)) for y in range(hs[j])]
    tot = 0
    for w in set(ws):
        R = [r for r in rows if ws[r[0]] == w]
        M = np.zeros((len(R), len(R)), dtype=int)
        for a, (j, y) in enumerate(R):
            pts = [idx[(j, y, x)] for x in range(w)]
            img = [c[p] for p in pts]
            for bb, (j2, y2) in enumerate(R):
                tgt = {idx[(j2, y2, x)]: x for x in range(w)}
                cnt = {}
                for x, q in enumerate(img):
                    if q in tgt: r = (tgt[q]-x) % w; cnt[r] = cnt.get(r, 0)+1
                M[a, bb] = w - max(cnt.values(), default=0)
        ri, ci = linear_sum_assignment(M); tot += int(M[ri, ci].sum())
    return tot

def alg_cost(ws, sig):
    """Majority-class regluing of the proof; returns cost and the per-cylinder deficits."""
    m = len(ws); best = []
    for j in range(m):
        cnt = {}
        for x in range(ws[j]):
            bj, bx = sig[(j, x)]
            if ws[bj] == ws[j]: key = (bj, (bx-x) % ws[j]); cnt[key] = cnt.get(key, 0)+1
        key, mx = max(cnt.items(), key=lambda kv: kv[1]) if cnt else (None, 0)
        best.append((key, mx))
    used = set(); cost = 0; rest = []
    for j in range(m):
        key, mx = best[j]
        if 2*mx > ws[j]:
            assert key[0] not in used; used.add(key[0]); cost += ws[j]-mx
        else: rest.append(j)
    free = [j for j in range(m) if j not in used]
    for j in rest:   # width-preserving completion exists
        k = next(q for q in free if ws[q] == ws[j] and q not in used); used.add(k); cost += ws[j]
    return cost, [ws[j]-best[j][1] for j in range(m)]

def has_break_everywhere(ws, sig):
    for j in range(len(ws)):
        ok = False
        for x in range(ws[j]):
            a, bb = sig[(j, x)], sig[(j, (x+1) % ws[j])]
            if not (a[0] == bb[0] and bb[1] == (a[1]+1) % ws[a[0]]): ok = True; break
        if not ok: return False
    return True

def check(ws, hs, sig, S, T):
    idx, b, c = build(ws, hs, sig)
    m = len(ws); W, H = max(ws), min(hs)
    rho = max(comm_rank(b, c, s, t)/(s+t) for s in range(1, S+1) for t in range(1, T+1))
    assert m <= 4*rho + 1e-9, ("m", m, rho)
    # Lemma U (top side), s = w_j, t = H
    for j in range(m):
        u = sum(1 for x in range(ws[j]) if ws[j] % ws[sig[(j, x)][0]] != 0)
        assert H*u <= N(b, c, ws[j], H), "lemma U"
    # Lemma V, t = H, all s < w_j
    for j in range(m):
        V = [x for x in range(ws[j]) if ws[sig[(j, x)][0]] == ws[j]]
        lhs = sum(sum(1 for x in V if sig[(j, (x+s) % ws[j])] !=
                      (sig[(j, x)][0], (sig[(j, x)][1]+s) % ws[j])) for s in range(ws[j]))
        rhs = sum(N(b, c, s, H) for s in range(1, ws[j]))
        assert H*lhs <= rhs, "lemma V"
    # Theorem 3 (height gap): a_{j,beta} min(h_j,h_beta) <= N(s, min h), s = w_j if w_beta !| w_j else w_beta
    for j in range(m):
        for be in range(m):
            if ws[be] == ws[j]: continue
            a = sum(1 for x in range(ws[j]) if sig[(j, x)][0] == be)
            if a == 0: continue
            tt = min(hs[j], hs[be]); ss = ws[j] if ws[j] % ws[be] else ws[be]
            assert a*tt <= N(b, c, ss, tt), "height gap"
    opt = opt_cost(ws, hs, idx, b, c); alg, _ = alg_cost(ws, sig)
    bound = rho*rho*(96 + 80*W/H)
    assert opt <= alg <= bound + 1e-9, (opt, alg, bound)
    return rho, opt, alg, W/H

def excised(n):
    """n x n torus minus the square (0,0): rows 1..n-1 form a width-n cylinder of height n-1,
    row 0 a width-(n-1) cylinder of height 1."""
    ws, hs = [n, n-1], [n-1, 1]; sig = {}
    for x in range(n): sig[(0, x)] = (1, x-1) if x > 0 else (0, 0)   # top of A: col 0 skips the hole
    for x in range(n-1): sig[(1, x)] = (0, x+1)                        # row 0 col x+1 -> row 1
    return ws, hs, sig

if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    worst_tall = 0; worst = 0; done = 0; tall = 0
    while done < trials:
        m = rng.randint(1, 4); ws = [rng.randint(1, 7) for _ in range(m)]
        if rng.random() < 0.5: ws = [rng.choice(ws[:1] + [rng.randint(1, 7)]) for _ in range(m)]
        hs = [rng.randint(1, 9) for _ in range(m)]
        sig = random_seam(ws, rng, rng.randint(1, 4))
        if not has_break_everywhere(ws, sig): continue
        rho, opt, alg, r = check(ws, hs, sig, 8, 10); done += 1
        worst = max(worst, alg/(rho*rho*(1+r)))
        if r <= 1: tall += 1; worst_tall = max(worst_tall, alg/rho**2)
    print(f"random: {done} surfaces checked (all lemma inequalities and opt <= alg <= bound hold)")
    print(f"  tall (H >= W): {tall}, max alg/rho_hat^2 = {worst_tall:.3f}; max alg/(rho^2 (1+W/H)) = {worst:.3f}")
    for n in range(3, 10):
        ws, hs, sig = excised(n); idx, b, c = build(ws, hs, sig)
        rho = max(comm_rank(b, c, s, t)/(s+t) for s in range(1, 2*n+1) for t in range(1, 2*n+1))
        print(f"  excised square n={n}: rho_hat={rho:.3f}, W/H={n}, exact b-fixed cost={opt_cost(ws, hs, idx, b, c)}")
