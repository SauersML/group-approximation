#!/usr/bin/env python3
"""Exact checks for Theorem K of
research/set-indexed-repetition-obeys-the-base-sdp-bound-on-keyed-hosts.md.

Theorem K: for every key kappa on the vertices of a bipartite unique game G,
every n and every tag count M,

    val(G_{tag,M}^{{n}})  >=  Pr[set win AND E]  =  Pr[ordered win(f) AND E]
                          >=  opt(G^n) - Pr[not E],
    Pr[not E]  <=  n theta(kappa) + C(n,2) q_A(kappa),

where E = {keys of u_1..u_n distinct and kappa(u_j) = kappa(v_j) for all j}
and f is the edge tuple reordered by sort-by-key composed with a shared
uniform permutation sigma.

All probabilities below are exact rationals (fractions.Fraction), computed by
full enumeration over edge tuples and over sigma in S_n. Checks:

  1. (exchangeability) the law of f is exactly w^{(x) n}  (n = 2, 3);
  2. (simulation identity) on E the set win equals the ordered win on f;
  3. (bound) sim value >= opt_ordered - Pr[not E] and
     Pr[not E] <= n theta + C(n,2) q_A;
  4. (n = 2, untagged, tiny) exact set value >= sim value.
Tagged games (M = 2) are built explicitly; the key ignores tags.
"""
import itertools
import random
from fractions import Fraction as Fr
from math import comb

import numpy as np


def random_game(nu, nv, k, n_edges, rng):
    """Bipartite UG: list of (u, v, perm, weight), weights rational, sum 1."""
    pairs = [(u, v) for u in range(nu) for v in range(nv)]
    chosen = rng.sample(pairs, n_edges)
    ws = [rng.randint(1, 4) for _ in chosen]
    tot = sum(ws)
    perms = list(itertools.permutations(range(k)))
    return [(u, v, rng.choice(perms), Fr(w, tot)) for (u, v), w in zip(chosen, ws)]


def disjoint_copies(game, nu, nv, c):
    out = []
    for i in range(c):
        for (u, v, p, w) in game:
            out.append((u + i * nu, v + i * nv, p, w / c))
    return out, nu * c, nv * c


def tag_blowup(game, M):
    """Vertices (u, a), (v, b); tags uniform, independent. Returns edges with
    left vertex (u, a) and right vertex (v, b)."""
    out = []
    for (u, v, p, w) in game:
        for a in range(M):
            for b in range(M):
                out.append(((u, a), (v, b), p, w / (M * M)))
    return out


def untag(x):
    return x[0] if isinstance(x, tuple) else x


def opt_ordered_2(game, nu, nv, k):
    """Exact opt(G^2) by brute force over Alice strategies (numpy search,
    then the maximiser is re-evaluated in exact rationals)."""
    qa_list = list(itertools.product(range(nu), repeat=2))
    qb_list = list(itertools.product(range(nv), repeat=2))
    lab = list(itertools.product(range(k), repeat=2))
    ia = {q: i for i, q in enumerate(qa_list)}
    ib = {q: i for i, q in enumerate(qb_list)}
    W = np.zeros((len(qa_list), len(qb_list), len(lab), len(lab)))
    Wx = {}
    for e1 in game:
        for e2 in game:
            p = e1[3] * e2[3]
            qa, qb = ia[(e1[0], e2[0])], ib[(e1[1], e2[1])]
            for a, la in enumerate(lab):
                for b, lb in enumerate(lab):
                    if lb[0] == e1[2][la[0]] and lb[1] == e2[2][la[1]]:
                        W[qa, qb, a, b] += float(p)
                        Wx[(qa, qb, a, b)] = Wx.get((qa, qb, a, b), 0) + p
    nqa, na = len(qa_list), len(lab)
    best, best_s = -1.0, None
    allS = np.array(list(itertools.product(range(na), repeat=nqa)))
    for c0 in range(0, len(allS), 4096):
        S = allS[c0:c0 + 4096]                       # (s, nqa)
        # T[s, qb, b] = sum_qa W[qa, qb, S[s, qa], b]
        T = np.zeros((len(S), W.shape[1], na))
        for qa in range(nqa):
            T += W[qa][:, S[:, qa], :].transpose(1, 0, 2)
        vals = T.max(axis=2).sum(axis=1)
        i = int(vals.argmax())
        if vals[i] > best:
            best, best_s = float(vals[i]), S[i].copy()
    # exact re-evaluation and Bob's best response
    tot = Fr(0)
    sb = {}
    for qb in range(len(qb_list)):
        cand = [sum((Wx.get((qa, qb, int(best_s[qa]), b), 0) for qa in range(nqa)), Fr(0))
                for b in range(na)]
        bb = max(range(na), key=lambda b: cand[b])
        sb[qb_list[qb]] = lab[bb]
        tot += cand[bb]
    sa = {qa_list[i]: lab[int(best_s[i])] for i in range(nqa)}
    return tot, sa, sb


def ordered_value(game, sa, sb, n):
    tot = Fr(0)
    for es in itertools.product(game, repeat=n):
        p = Fr(1)
        for e in es:
            p *= e[3]
        la = sa[tuple(untag(e[0]) for e in es)]
        lb = sb[tuple(untag(e[1]) for e in es)]
        if all(lb[j] == es[j][2][la[j]] for j in range(n)):
            tot += p
    return tot


def random_ordered_strategy(nu, nv, k, n, rng):
    sa = {q: tuple(rng.randrange(k) for _ in range(n))
          for q in itertools.product(range(nu), repeat=n)}
    sb = {q: tuple(rng.randrange(k) for _ in range(n))
          for q in itertools.product(range(nv), repeat=n)}
    return sa, sb


def key_costs(base, key, n):
    """theta, q_A of a key given as dict on ('L', u) and ('R', v)."""
    theta = sum((e[3] for e in base if key[('L', e[0])] != key[('R', e[1])]), Fr(0))
    muA = {}
    for e in base:
        muA[e[0]] = muA.get(e[0], 0) + e[3]
    cls = {}
    for u, m in muA.items():
        cls[key[('L', u)]] = cls.get(key[('L', u)], 0) + m
    qA = sum((m * m for m in cls.values()), Fr(0))
    return theta, qA, n * theta + comb(n, 2) * qA


def simulate(game, key, sa, sb, n):
    """Exact analysis of the key simulation of ordered strategy (sa, sb) on
    the set game of `game` (tagged or not).  Returns a dict of exact values."""
    kL = lambda x: key[('L', untag(x))]
    kR = lambda y: key[('R', untag(y))]
    perms = list(itertools.permutations(range(n)))
    inv = Fr(1, len(perms))
    P = dict(good=Fr(0), E=Fr(0), win_good=Fr(0), win_E=Fr(0),
             ordwin_f_E=Fr(0), ordwin_f=Fr(0), E_not_good=Fr(0),
             mismatch_on_E=0)
    law_f = {}
    for es in itertools.product(game, repeat=n):
        p = Fr(1)
        for e in es:
            p *= e[3]
        us = [e[0] for e in es]
        vs = [e[1] for e in es]
        good = len(set(us)) == n and len(set(vs)) == n
        E = (len({kL(u) for u in us}) == n
             and all(kL(es[j][0]) == kR(es[j][1]) for j in range(n)))
        if good:
            P['good'] += p
        if E:
            P['E'] += p
            if not good:
                P['E_not_good'] += p
        # tau: index order of Alice's elements sorted by (key, id)
        tau = sorted(range(n), key=lambda j: (kL(us[j]), us[j]))
        xs = [us[j] for j in tau]
        ys = sorted(vs, key=lambda y: (kR(y), y))
        for sg in perms:
            # Alice: x_{sigma(i)} gets label i of sa(untag tuple)
            la = sa[tuple(untag(xs[sg[i]]) for i in range(n))]
            lb = sb[tuple(untag(ys[sg[i]]) for i in range(n))]
            alpha = {xs[sg[i]]: la[i] for i in range(n)}
            beta = {ys[sg[i]]: lb[i] for i in range(n)}
            f = tuple(es[tau[sg[i]]] for i in range(n))
            law_f[f] = law_f.get(f, 0) + p * inv
            # ordered win of (sa, sb) on the tuple f itself (not the set play)
            fa = sa[tuple(untag(e[0]) for e in f)]
            fb = sb[tuple(untag(e[1]) for e in f)]
            ow = all(fb[i] == f[i][2][fa[i]] for i in range(n))
            if ow:
                P['ordwin_f'] += p * inv
            if good:
                sw = all(beta[es[j][1]] == es[j][2][alpha[es[j][0]]]
                         for j in range(n))
                if sw:
                    P['win_good'] += p * inv
                if E:
                    if sw:
                        P['win_E'] += p * inv
                    if ow:
                        P['ordwin_f_E'] += p * inv
                    if sw != ow:
                        P['mismatch_on_E'] += 1
    # exchangeability: law of f equals the product law
    maxdev = Fr(0)
    for es in itertools.product(game, repeat=n):
        p = Fr(1)
        for e in es:
            p *= e[3]
        maxdev = max(maxdev, abs(law_f.get(es, 0) - p))
    P['law_f_maxdev'] = maxdev
    P['sim_value'] = P['win_good'] / P['good']
    return P


def all_partitions(items):
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for part in all_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1:]
        yield [[first]] + part


def key_from_partition(part):
    return {x: r for r, blk in enumerate(part) for x in blk}


def set_value_2(game, k):
    """Exact val(G^{{2}}) (untagged, small): brute force over Alice's
    labellings of each 2-set, Bob best-responds."""
    Asets = sorted({tuple(sorted((e1[0], e2[0]))) for e1 in game for e2 in game
                    if e1[0] != e2[0]})
    lab = list(itertools.product(range(k), repeat=2))
    W = {}
    pg = Fr(0)
    for e1 in game:
        for e2 in game:
            if e1[0] == e2[0] or e1[1] == e2[1]:
                continue
            p = e1[3] * e2[3]
            pg += p
            A = tuple(sorted((e1[0], e2[0])))
            B = tuple(sorted((e1[1], e2[1])))
            for ia, la in enumerate(lab):
                al = dict(zip(A, la))
                for ib, lb in enumerate(lab):
                    be = dict(zip(B, lb))
                    if all(be[e[1]] == e[2][al[e[0]]] for e in (e1, e2)):
                        W[(A, B, ia, ib)] = W.get((A, B, ia, ib), 0) + p
    Bsets = sorted({key[1] for key in W})
    best = Fr(-1)
    for S in itertools.product(range(len(lab)), repeat=len(Asets)):
        s = dict(zip(Asets, S))
        tot = Fr(0)
        for B in Bsets:
            tot += max(sum((W.get((A, B, s[A], ib), 0) for A in Asets), Fr(0))
                       for ib in range(len(lab)))
        best = max(best, tot)
    return best / pg


def block_game(k, rng):
    """3+3 vertices, edges only inside blocks {0,1}x{0,1} and {2}x{2}."""
    perms = list(itertools.permutations(range(k)))
    pairs = [(0, 0), (0, 1), (1, 0), (1, 1), (2, 2)]
    ws = [rng.randint(1, 4) for _ in pairs]
    tot = sum(ws)
    return [(u, v, rng.choice(perms), Fr(w, tot)) for (u, v), w in zip(pairs, ws)]


def check_case(name, game, base, nu, nv, k, n, sa, sb, ordval, keys, setval=None):
    worst_gap = None
    best_bound = None
    for key in keys:
        th, qA, cost = key_costs(base, key, n)
        P = simulate(game, key, sa, sb, n)
        assert P['law_f_maxdev'] == 0, name
        assert P['mismatch_on_E'] == 0, name
        assert P['E_not_good'] == 0, name
        assert P['win_E'] == P['ordwin_f_E'], name
        assert P['ordwin_f'] == ordval, name
        notE = 1 - P['E']
        assert notE <= cost, name
        assert P['sim_value'] >= P['win_E'] >= ordval - notE, name
        if setval is not None:
            assert setval >= P['sim_value'], name
        g = P['sim_value'] - (ordval - cost)
        worst_gap = g if worst_gap is None else min(worst_gap, g)
        b = ordval - cost
        best_bound = b if best_bound is None else max(best_bound, b)
    print(f"{name}: keys={len(keys)} ordered={float(ordval):.4f} "
          f"best(opt-cost)={float(best_bound):.4f} "
          + (f"set_val={float(setval):.4f} " if setval is not None else "")
          + f"min(sim-(opt-cost))={float(worst_gap):.4f}  OK")


def main():
    rng = random.Random(20260920)
    k = 2
    verts = [('L', u) for u in range(3)] + [('R', v) for v in range(3)]
    parts = list(all_partitions(verts))
    keys_all = [key_from_partition(p) for p in parts]
    print(f"[1] n=2, untagged, all {len(keys_all)} keys, exact opt(G^2), exact set value")
    for t in range(4):
        g = block_game(k, rng) if t % 2 == 0 else random_game(3, 3, k, 6, rng)
        opt2, sa, sb = opt_ordered_2(g, 3, 3, k)
        assert ordered_value(g, sa, sb, 2) == opt2
        sv = set_value_2(g, k)
        check_case(f"  game{t}", g, g, 3, 3, k, 2, sa, sb, opt2, keys_all, sv)
    print("[2] n=2, tagged M=2 (key ignores tags), all keys, ordered = opt(G^2)")
    for t in range(2):
        g = block_game(k, rng) if t == 0 else random_game(3, 3, k, 5, rng)
        opt2, sa, sb = opt_ordered_2(g, 3, 3, k)
        gt = tag_blowup(g, 2)
        check_case(f"  tagged{t}", gt, g, 3, 3, k, 2, sa, sb, opt2, keys_all)
    print("[3] n=3, tagged M=2, random ordered strategies, 6 random keys each")
    for t in range(2):
        g = block_game(k, rng) if t == 0 else random_game(3, 3, k, 5, rng)
        sa, sb = random_ordered_strategy(3, 3, k, 3, rng)
        gt = tag_blowup(g, 2)
        ov = ordered_value(g, sa, sb, 3)
        assert ordered_value(gt, sa, sb, 3) == ov
        keys = rng.sample(keys_all, 6)
        check_case(f"  tagged-n3-{t}", gt, g, 3, 3, k, 3, sa, sb, ov, keys)
    print("[4] odd cycle C_m: exact key cost z_n over all partitions of the 2m-cycle")
    print("    host of the w21 node: y = x + d, d = 0 w.p. 1/2, d = +-1 w.p. 1/4 each")
    print("    claim: z_n(C_m) >= min(n^2/4, n^{3/2}/(2 sqrt m))  (Lemma C of the route)")
    for m in (3, 5):
        cyc = []
        for x in range(m):
            cyc.append((x, x, None, Fr(1, 2 * m)))
            cyc.append((x, (x + 1) % m, None, Fr(1, 4 * m)))
            cyc.append((x, (x - 1) % m, None, Fr(1, 4 * m)))
        vs = [('L', x) for x in range(m)] + [('R', y) for y in range(m)]
        stats = []
        for p in all_partitions(vs):
            key = key_from_partition(p)
            th, qA, _ = key_costs(cyc, key, 1)
            stats.append((th, qA))
        for n in (2, 3, 5, 10, 20, 40):
            z = min(n * th + comb(n, 2) * qA for th, qA in stats)
            lb = min(n * n / 4, n ** 1.5 / (2 * m ** 0.5))
            assert float(z) >= lb - 1e-12
            print(f"    m={m} n={n:3d}  z_n={float(z):9.4f}  lower={lb:9.4f}")
    print("[5] noisy-hypercube host, subcube keys (codim t): cost <= n t eta + C(n,2) 2^-t,")
    print("    n = eps'/eta; smallest cost over t (keyed iff well below 1 - delta')")
    for eps in (0.1, 0.05, 0.02):
        row = []
        for logr in (5, 10, 20, 40, 80):
            n = 2 ** logr                # n = eps'/eta
            eta = eps / n
            best = min(n * t * eta + comb(n, 2) * 2.0 ** (-t) for t in range(1, 400))
            row.append(f"eps'/eta=2^{logr}: {best:.3f}")
        print(f"    eps'={eps}: " + ", ".join(row))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
