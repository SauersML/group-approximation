"""Mechanical check of the combinatorial core of the hierarchical-class kill.

Claim: research/thompson-f-hierarchical-size-laws-die-at-width-four.md.
For a base configuration (m, d) of width 4 we check, over {0,1}-valued level
functions b on the non-extreme depth-d leaves (thresholds [level >= t] of any
real level function, which preserve every max-equality):

  step a  domination: for every position j and words s, t whose j-th middle
          pieces are nodes x, y with leaves(x) strictly containing leaves(y),
          impose max_x b = max_y b;
  step b  equal laws of the middle level vectors: whenever coordinates i, j of
          one word agree for every admissible b, impose "coordinates i, j agree"
          for every word, and iterate to a fixpoint (for (0,4), (1,3), (2,2) one
          word already has a forced-constant vector, which forces the diagonal
          at once; for (3,1) two rounds are needed);
  step c  after the fixpoint only b = 0 and b = 1 survive;
  step d  a ratio pair exists: words s, t with the same node at a middle
          position i and strictly nested nodes at a middle position j != i.
Steps a-d are all the proof uses about the Guba set; see the claim file.
Usage: python3 hierarchical_kill.py [m d ...]   (default: 0 4 1 3 2 2 3 1)
"""
import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "thompson-f-size-observation-2026-09-17"))
from level_search import monomial_set  # noqa: E402
from equal_middle_lp import antichain, leaves  # noqa: E402


def check(m, d):
    S = monomial_set(m, d)
    LV = leaves(m, d)
    n = len(LV)
    mids = [antichain(m, w)[1:-1] for w in S]
    w = m + d
    assert all(len(p) == w - 1 for p in mids)

    def lset(node):
        a, q = node
        return frozenset(i for i, (b, r) in enumerate(LV) if b == a and r.startswith(q))

    L = [[lset(x) for x in p] for p in mids]
    assert all(L[s][j] for s in range(len(S)) for j in range(w - 1)), "middle piece without middle leaf"
    covered = set().union(*[x for p in L for x in p])
    assert covered == set(range(n)), "some non-extreme leaf lies in no middle piece"

    dom = set()
    for j in range(w - 1):
        for s, t in itertools.permutations(range(len(S)), 2):
            if L[s][j] > L[t][j]:
                dom.add((L[s][j], L[t][j], j, s, t))
    B = np.array(list(itertools.product((0, 1), repeat=n)), dtype=np.int8)

    def mx(X):
        return B[:, sorted(X)].max(axis=1)

    ok = np.ones(len(B), dtype=bool)
    for X, Y, *_ in dom:
        ok &= mx(X) == mx(Y)
    Ba = ok.copy()
    vec = [np.stack([mx(X) for X in p], 1) for p in L]
    const = [s for s in range(len(S)) if np.all(vec[s][Ba].min(1) == vec[s][Ba].max(1))]
    # step b': propagate coordinate equalities through equal vector laws.  If
    # coordinates i, j of word s agree for every admissible b, they agree a.s. for
    # the real levels, hence (equal laws) for every word t; impose that and repeat.
    cur = Ba.copy()
    forced = set()
    rounds = 0
    while True:
        rounds += 1
        new = set()
        for s in range(len(S)):
            for i, j in itertools.combinations(range(w - 1), 2):
                if (i, j) not in forced and np.all(vec[s][cur, i] == vec[s][cur, j]):
                    new.add((i, j))
        if not new:
            break
        forced |= new
        for i, j in new:
            for t in range(len(S)):
                cur &= vec[t][:, i] == vec[t][:, j]
    diag = cur
    surv = sorted(tuple(int(v) for v in B[i]) for i in np.where(diag)[0])
    ratio = None
    for s, t in itertools.permutations(range(len(S)), 2):
        for i in range(w - 1):
            if mids[s][i] != mids[t][i]:
                continue
            for j in range(w - 1):
                if j != i and L[s][j] > L[t][j]:
                    ratio = (s, t, i, j)
                    break
            if ratio:
                break
        if ratio:
            break
    fmt = lambda nd: f"{nd[0]}:{nd[1] or 'root'}"
    print(f"(m,d)=({m},{d}) width {w}: words={len(S)} middle leaves={n} domination pairs={len(dom)}")
    print(f"  step a: {int(Ba.sum())} of {len(B)} Boolean level functions satisfy domination")
    print(f"  step b: words with forced-constant middle vector: {len(const)}; e.g. "
          f"{[fmt(x) for x in mids[const[0]]] if const else None}")
    print(f"  step b': forced coordinate equalities {sorted((i+1, j+1) for i, j in forced)} "
          f"after {rounds} rounds")
    print(f"  step c: survivors of domination + forced equalities: {len(surv)} "
          f"({'only constants' if surv == [(0,)*n, (1,)*n] else 'NOT only constants'})")
    if ratio:
        s, t, i, j = ratio
        print(f"  step d: ratio pair: shared {fmt(mids[s][i])} at position {i+1}; "
              f"{fmt(mids[s][j])} strictly contains {fmt(mids[t][j])} at position {j+1}")
    good = surv == [(0,) * n, (1,) * n] and ratio is not None and bool(dom)
    print(f"  VERDICT: {'hierarchical class killed' if good else 'check FAILED'}")
    return good


if __name__ == "__main__":
    a = list(map(int, sys.argv[1:])) or [0, 4, 1, 3, 2, 2, 3, 1]
    res = [check(a[k], a[k + 1]) for k in range(0, len(a), 2)]
    print("ALL PASS" if all(res) else "SOME FAILED")
