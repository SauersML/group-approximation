#!/usr/bin/env python3
"""Monte Carlo fibre profile of Bernoulli bond percolation on Cayley graphs of F_2 x Z.

Lane bs-pc-pu, 2026-09-12. Plausibility check for the open premises of
research/fpbs-hyperbolic-quotient-fibre-estimates-l2-gap.md:
  (i)  fibre bubble  B = sum_q sigma_p(q)^2,
  (ii) far-halfspace share, measured on tree branches,
together with chi_p, chi^H_p = sigma_p(1), sigma_p(s) and E|pi(K)|/chi_p.
Clusters are explored lazily on the infinite graph and capped at CAP vertices.
Run through the msi wrapper only.

Usage: fibre_profile_mc.py GENSET p1,p2,... NSAMPLES CAP SEED
GENSET is a ';'-separated list of letter:height with letters in a,b,1
(inverses are added automatically), e.g. 'a:0;b:0;1:1'.
"""
import sys, random, json
from collections import deque, defaultdict

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b', '1': '1'}


def mul(w, letter):
    if letter == '1':
        return w
    if w and w[-1] == INV[letter]:
        return w[:-1]
    return w + letter


def parse(genset):
    gens = []
    for tok in genset.split(';'):
        l, k = tok.split(':')
        gens.append((l, int(k)))
    full = []
    for l, k in gens:
        full.append((l, k))
        full.append((INV[l], -k))
    seen, out = set(), []
    for g in full:
        if g not in seen and g != ('1', 0):
            seen.add(g)
            out.append(g)
    idx = {g: i for i, g in enumerate(out)}
    inv = [idx[(INV[l], -k)] for (l, k) in out]
    return out, inv


def explore(gens, inv, p, cap, rng):
    status = {}
    root = ('', 0)
    seen = {root}
    dq = deque([root])
    while dq:
        v = dq.popleft()
        w, h = v
        for i, (l, k) in enumerate(gens):
            u = (mul(w, l), h + k)
            key = (v, i) if (v, i) < (u, inv[i]) else (u, inv[i])
            s = status.get(key)
            if s is None:
                s = rng.random() < p
                status[key] = s
            if s and u not in seen:
                seen.add(u)
                if len(seen) > cap:
                    return seen, True
                dq.append(u)
    return seen, False


def run(genset, p, n, cap, seed, dmax=6):
    gens, inv = parse(genset)
    rng = random.Random(seed)
    tot = 0.0; totH = 0.0; totfib = 0.0; trunc = 0
    sig = [defaultdict(float), defaultdict(float)]
    branch = [defaultdict(float) for _ in range(dmax + 1)]
    for t in range(n):
        K, tr = explore(gens, inv, p, cap, rng)
        trunc += tr
        m = defaultdict(int)
        for (w, h) in K:
            m[w] += 1
        tot += len(K); totH += m.get('', 0); totfib += len(m)
        half = sig[t % 2]
        for w, c in m.items():
            half[w] += c
            for D in range(1, min(len(w), dmax) + 1):
                branch[D][w[:D]] += c
    chi = tot / n
    s1 = {w: 2.0 * c / n for w, c in sig[0].items()}
    s2 = {w: 2.0 * c / n for w, c in sig[1].items()}
    B = sum(s1[w] * s2.get(w, 0.0) for w in s1)
    sigma = {w: (sig[0][w] + sig[1][w]) / n for w in set(sig[0]) | set(sig[1])}
    out = {
        'genset': genset, 'p': p, 'n': n, 'cap': cap, 'trunc_frac': trunc / n,
        'chi': chi, 'chiH': totH / n, 'fibres_over_chi': (totfib / n) / chi,
        'sigma_letters': {l: sigma.get(l, 0.0) for l in 'aAbB'},
        'fibre_bubble_split': B,
        'max_sigma_depth': {D: max([sigma[w] for w in sigma if len(w) == D] or [0.0])
                            for D in range(1, dmax + 1)},
        'max_branch_share_depth': {D: max(list(branch[D].values()) or [0.0]) / n / chi
                                   for D in range(1, dmax + 1)},
    }
    return out


if __name__ == '__main__':
    genset, ps, n, cap, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    for j, p in enumerate(float(x) for x in ps.split(',')):
        print(json.dumps(run(genset, p, n, cap, seed + 1000 * j)), flush=True)
