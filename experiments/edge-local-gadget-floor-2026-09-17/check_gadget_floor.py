#!/usr/bin/env python3
"""Exhaustive replay of the local-gadget random-assignment floor.

Claim: research/local-gadgets-above-exactness-pay-a-random-assignment-floor.md

Setting.  A patch N = {0, ..., k-1} of primaries with alphabets [K_z], a local
satisfying set S <= prod_z [K_z] (for an outer edge: the relation R_e), and a
gadget: auxiliary vertices with arbitrary alphabets and weighted constraints
(total weight 1).  A constraint whose scope meets at least two primaries must
contain only primaries ("direct" constraint); all other scopes are arbitrary.

  v(x)   = max over auxiliary assignments of the satisfied weight
  h(x)   = satisfied weight of direct constraints (independent of aux)
  c      = E_{x ~ uniform on S} v(x)            (oblivious completeness)
  ex     = E_{x ~ uniform on S} h(x)            (direct exactness)
  floor  = E_{x ~ uniform on prod [K_z]} v(x)   (random-assignment value)
  M      = max_z max_t Pr_S[x_z = t] * K_z      (marginal density of S)
  r_z(t) = min { v(x) : x_z = t }

Checked statements:
  (P) v(x) - h(x) <= sum_z r_z(x_z)                for every x
  (F) c - ex <= M * k * floor
  (E) for a d-to-d or 2-to-1 relation and permutation direct constraints of
      total weight W:  ex <= W / d
Tightness replays:
  split gadget (two branch permutations, weight 1/2):  c = 1/2 = ex, floor = 1/K
  block-projection gadget (non-unique aux, 2-to-2):     c = 1, ex = 0,
      floor = 1/2 + 1/K, so (F) is tight as K grows.

Usage: nice -n 10 timeout 1200 python3 check_gadget_floor.py [seed] [trials]
Exit code 0 means PASS.
"""
import itertools
import random
import sys
from fractions import Fraction


def eval_gadget(sizes, aux_sizes, cons):
    """Return v, h as dicts over prod [sizes]."""
    k = len(sizes)
    aux_assign = list(itertools.product(*[range(s) for s in aux_sizes]))
    direct = [c for c in cons if all(i < k for i in c[1]) and len(c[1]) >= 2]
    other = [c for c in cons if c not in direct]
    v, h = {}, {}
    for x in itertools.product(*[range(s) for s in sizes]):
        hx = sum(w for (w, sc, pred) in direct if tuple(x[i] for i in sc) in pred)
        best = None
        for a in aux_assign:
            lab = x + a
            t = sum(w for (w, sc, pred) in other if tuple(lab[i] for i in sc) in pred)
            if best is None or t > best:
                best = t
        v[x] = best + hx
        h[x] = hx
    return v, h


def check(sizes, S, v, h):
    k = len(sizes)
    allx = list(v.keys())
    r = [dict() for _ in range(k)]
    for z in range(k):
        for t in range(sizes[z]):
            r[z][t] = min(v[x] for x in allx if x[z] == t)
    okP = all(v[x] - h[x] <= sum(r[z][x[z]] for z in range(k)) + 1e-12 for x in allx)
    c = sum(v[x] for x in S) / len(S)
    ex = sum(h[x] for x in S) / len(S)
    floor = sum(v.values()) / len(allx)
    M = max(sum(1 for x in S if x[z] == t) * sizes[z] / len(S)
            for z in range(k) for t in range(sizes[z]))
    okF = c - ex <= M * k * floor + 1e-12
    return okP, okF, c, ex, floor, M


def dd_relation(K, d, rng):
    left = list(range(K)); right = list(range(K))
    rng.shuffle(left); rng.shuffle(right)
    return [(x, y) for b in range(K // d)
            for x in left[b * d:(b + 1) * d] for y in right[b * d:(b + 1) * d]]


def two_to_one(n, rng):
    left = list(range(2 * n)); rng.shuffle(left)
    return [(left[i], i // 2) for i in range(2 * n)]


def perm_pred(K, rng, keep=1.0):
    p = list(range(K)); rng.shuffle(p)
    return {(i, p[i]) for i in range(K) if rng.random() < keep}


def random_gadget(sizes, rng, unique):
    k = len(sizes)
    m = rng.randint(0, 2)
    aux = [sizes[0] if unique else rng.randint(2, 4) for _ in range(m)]
    allsz = list(sizes) + aux
    nv = len(allsz)
    cons = []
    for _ in range(rng.randint(1, 6)):
        if unique:
            cand = [(a, b) for a in range(nv) for b in range(a + 1, nv) if allsz[a] == allsz[b]]
            if not cand:
                cand = [(a, b) for a in range(nv) for b in range(a + 1, nv)]
            sc = rng.choice(cand)
            if allsz[sc[0]] == allsz[sc[1]]:
                pred = perm_pred(allsz[sc[0]], rng)
            else:
                K1 = min(allsz[sc[0]], allsz[sc[1]])
                p = rng.sample(range(max(allsz[sc[0]], allsz[sc[1]])), K1)
                pred = {(i, p[i]) for i in range(K1)} if allsz[sc[0]] <= allsz[sc[1]] \
                    else {(p[i], i) for i in range(K1)}
        else:
            ar = rng.randint(1, min(3, nv))
            sc = tuple(sorted(rng.sample(range(nv), ar)))
            prim = [i for i in sc if i < k]
            if len(prim) >= 2:
                sc = tuple(prim)  # direct constraint: primaries only
            tuples = list(itertools.product(*[range(allsz[i]) for i in sc]))
            pred = {t for t in tuples if rng.random() < 0.4}
        cons.append((rng.random(), tuple(sc), pred))
    tw = sum(c[0] for c in cons)
    return aux, [(w / tw, sc, p) for (w, sc, p) in cons]


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20260917
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    rng = random.Random(seed)
    worst_ratio = 0.0
    for trial in range(trials):
        kind = trial % 4
        if kind == 0:
            sizes, d = (4, 4), 2; S = dd_relation(4, 2, rng)
        elif kind == 1:
            sizes, d = (6, 6), 3; S = dd_relation(6, 3, rng)
        elif kind == 2:
            n = rng.choice([2, 3]); sizes, d = (2 * n, n), 2; S = two_to_one(n, rng)
        else:
            # triangle patch with a random nonempty local satisfying set
            sizes, d = (3, 3, 3), None
            allx = list(itertools.product(range(3), range(3), range(3)))
            S = [x for x in allx if rng.random() < 0.3] or [allx[0]]
        unique = (trial % 2 == 0)
        aux, cons = random_gadget(sizes, rng, unique)
        v, h = eval_gadget(sizes, aux, cons)
        okP, okF, c, ex, floor, M = check(sizes, S, v, h)
        okE = True
        if d is not None and unique:
            W = sum(w for (w, sc, p) in cons if sc == (0, 1))
            okE = ex <= W / d + 1e-12
        if not (okP and okF and okE):
            print('VIOLATION', trial, sizes, okP, okF, okE, c, ex, floor, M)
            sys.exit(1)
        if floor > 0:
            worst_ratio = max(worst_ratio, (c - ex) / (M * len(sizes) * floor))
    print(f'random gadgets checked: {trials}; (P), (F), (E) hold on all; '
          f'max (c-ex)/(M k floor) = {worst_ratio:.4f}')

    # tightness 1: split gadget on a 2-to-2 relation
    for K in (4, 8):
        S = [(x, y) for x in range(K) for y in range(K) if x // 2 == y // 2]
        cons = [(Fraction(1, 2), (0, 1), {(i, i) for i in range(K)}),
                (Fraction(1, 2), (0, 1), {(i, i ^ 1) for i in range(K)})]
        v, h = eval_gadget((K, K), [], cons)
        okP, okF, c, ex, floor, M = check((K, K), S, v, h)
        assert okP and okF and c == Fraction(1, 2) and ex == Fraction(1, 2) and floor == Fraction(1, K)
        print(f'split K={K}: c={c} ex={ex} floor={floor}')
    # tightness 2: block-projection gadget (aux u = block index, non-unique)
    for K in (4, 8):
        S = [(x, y) for x in range(K) for y in range(K) if x // 2 == y // 2]
        proj = {(t, t // 2) for t in range(K)}
        cons = [(Fraction(1, 2), (0, 2), proj), (Fraction(1, 2), (1, 2), proj)]
        v, h = eval_gadget((K, K), [K // 2], cons)
        okP, okF, c, ex, floor, M = check((K, K), S, v, h)
        assert okP and okF and c == 1 and ex == 0 and floor == Fraction(1, 2) + Fraction(1, K)
        print(f'block projection K={K}: c={c} ex={ex} floor={floor} = 1/2 + 1/K '
              f'-> (F) reads 1 <= {M * 2 * floor}, tight as K grows')
    print('PASS')


if __name__ == '__main__':
    main()
