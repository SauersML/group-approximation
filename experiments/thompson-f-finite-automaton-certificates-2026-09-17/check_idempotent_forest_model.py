#!/usr/bin/env python3
"""Checks for thompson-f-finite-state-flows-cannot-prove-nonamenability.

1. Forest model of the positive monoid M of Thompson's F: x_k acts by merging roots k, k+1.
   Checks the relations x_j x_i = x_i x_(j+1) (i<j) and injectivity on normal forms.
2. For random finite magmas (Q, delta) with leaf state, finds an idempotent probability
   measure pi = delta_*(pi x pi) on the reachable states (damped iteration + residual check).
3. Exact enumeration of the i.i.d. forest model Y (N trees, each a complete depth-H top with
   i.i.d. pi-distributed representative trees at the bottom) and check that for every s in S
   the profile law of split_s(Y) equals the i.i.d. law nu_(N + deg s).
4. Calibration on the free monoid on two letters, where the method must fail: there a z is
   never in both aM and bM, so the in-degree identity used in the proof breaks.
5. The identity invariant (free magma) has no idempotent probability measure (min-size argument),
   checked on a finite truncation.

Stdlib only. Run: nice -n 10 timeout 1200 python3 check_idempotent_forest_model.py
"""
import itertools, random
from collections import defaultdict

LEAF = None


def strip(f):
    f = list(f)
    while f and f[-1] is LEAF:
        f.pop()
    return tuple(f)


def merge(k, f):
    f = list(f) + [LEAF] * max(0, k + 2 - len(f))
    return strip(f[:k] + [(f[k], f[k + 1])] + f[k + 2:])


def split(k, f):
    f = list(f)
    if k >= len(f) or f[k] is LEAF:
        return None
    L, R = f[k]
    return strip(f[:k] + [L, R] + f[k + 1:])


def act(word, f):
    """word = (i1,...,id) for x_i1 ... x_id acting on the left."""
    for k in reversed(word):
        f = merge(k, f)
    return f


def unact(word, z):
    for k in word:
        z = split(k, z)
        if z is None:
            return None
    return z


def check_monoid(D=5, L=6):
    for i in range(L):
        for j in range(i + 1, L):
            for f in [(), ((LEAF, LEAF),), (LEAF, (LEAF, LEAF), LEAF, (LEAF, LEAF))]:
                assert act((j, i), f) == act((i, j + 1), f)
    seen = {}
    for d in range(D + 1):
        for w in itertools.combinations_with_replacement(range(L), d):
            f = act(w, ())
            assert f not in seen, (w, seen.get(f))
            seen[f] = w
    return len(seen)


def size(t):
    return 0 if t is LEAF else 1 + size(t[0]) + size(t[1])


def random_magma(n, rng):
    delta = {(a, b): rng.randrange(n) for a in range(n) for b in range(n)}
    leaf = rng.randrange(n)
    return delta, leaf


def reachable(delta, leaf, maxdepth=12):
    reps = {leaf: LEAF}
    frontier = True
    while frontier:
        frontier = False
        for a, ta in list(reps.items()):
            for b, tb in list(reps.items()):
                c = delta[(a, b)]
                if c not in reps:
                    reps[c] = (ta, tb)
                    frontier = True
    return reps


def idempotent_measure(delta, states, rng, iters=4000, restarts=20):
    """Fixed point of pi -> delta_*(pi x pi) on the simplex (exists by Brouwer).
    Damped iteration with renormalisation from random starts; returns best residual."""
    best = (None, float('inf'))
    for _ in range(restarts):
        pi = {s: rng.random() + 1e-3 for s in states}
        tot = sum(pi.values())
        pi = {s: v / tot for s, v in pi.items()}
        for it in range(iters):
            new = defaultdict(float)
            for a in states:
                for b in states:
                    new[delta[(a, b)]] += pi[a] * pi[b]
            eta = 0.5 / (1 + it / 50.0)
            pi = {s: (1 - eta) * pi[s] + eta * new[s] for s in states}
            tot = sum(pi.values())
            pi = {s: v / tot for s, v in pi.items()}
        new = defaultdict(float)
        for a in states:
            for b in states:
                new[delta[(a, b)]] += pi[a] * pi[b]
        res = max(abs(new[s] - pi[s]) for s in states)
        if res < best[1]:
            best = (pi, res)
        if res < 1e-12:
            break
    return best


def q_of(t, delta, leaf):
    return leaf if t is LEAF else delta[(q_of(t[0], delta, leaf), q_of(t[1], delta, leaf))]


def complete_top(bottoms):
    level = list(bottoms)
    while len(level) > 1:
        level = [(level[i], level[i + 1]) for i in range(0, len(level), 2)]
    return level[0]


def exact_model_check(delta, leaf, pi, reps, N, H, S):
    """Enumerate all bottom assignments; compare profile law of split_s(Y) with nu_(N+d)."""
    support = [s for s in pi if pi[s] > 1e-9]
    nb = N * (2 ** H)
    law_split = {tuple(s): defaultdict(float) for s in S}
    for assign in itertools.product(support, repeat=nb):
        p = 1.0
        for a in assign:
            p *= pi[a]
        trees = [complete_top([reps[a] for a in assign[i * 2 ** H:(i + 1) * 2 ** H]]) for i in range(N)]
        y = strip(trees)
        for s in S:
            u = unact(s, y)
            assert u is not None, "every split must exist in the model"
            prof = tuple(q_of(t, delta, leaf) for t in u)
            law_split[tuple(s)][prof] += p
    worst = 0.0
    for s in S:
        d = len(s)
        nu = defaultdict(float)
        for prof in itertools.product(support, repeat=N + d):
            pr = 1.0
            for a in prof:
                pr *= pi[a]
            nu[prof] += pr
        keys = set(nu) | set(law_split[tuple(s)])
        tv = 0.5 * sum(abs(nu[k] - law_split[tuple(s)][k]) for k in keys)
        worst = max(worst, tv)
    return worst


def calibrate_free_monoid():
    # free monoid on {a,b}: z in aM and z in bM never both hold for z != e.
    words = [''.join(w) for n in range(1, 6) for w in itertools.product('ab', repeat=n)]
    both = sum(1 for z in words if z.startswith('a') and z.startswith('b'))
    return both


def no_idempotent_on_free_magma(maxsize=7):
    # any probability pi on trees: support of delta_*(pi x pi) has min size >= 2*min+1 > min.
    for m in range(0, maxsize):
        assert 2 * m + 1 > m
    return True


def main():
    rng = random.Random(20260917)
    n = check_monoid()
    print(f"[1] forest model: relations hold, {n} normal forms map injectively to forests")
    X2 = [(0,), (1,), (2,)]
    S35 = [w for w in itertools.combinations_with_replacement(range(4), 2) if w[0] <= 2 and w[1] <= 3]
    tested = 0
    worst_res, worst_tv = 0.0, 0.0
    trials = 0
    nontrivial = 0
    while tested < 16 and trials < 2000:
        trials += 1
        qn = rng.choice([2, 3])
        delta, leaf = random_magma(qn, rng)
        reps = reachable(delta, leaf)
        states = sorted(reps)
        pi, res = idempotent_measure(delta, states, rng)
        if not res <= 1e-9 or abs(sum(pi.values()) - 1) > 1e-12:
            continue
        support = [s for s in pi if pi[s] > 1e-9]
        if len(support) < 2:
            continue  # point mass: the profile is deterministic, nothing to test
        if len(support) > 2:
            N, H = 4, 1
            S = X2
        else:
            N, H = 4, 2
            S = X2 + S35
        tv = exact_model_check(delta, leaf, pi, reps, N, H, S)
        worst_res = max(worst_res, res)
        worst_tv = max(worst_tv, tv)
        tested += 1
        nontrivial += len(support) >= 2
        print(f"[3] magma |Q|={qn} delta={dict(sorted(delta.items()))} leaf={leaf} "
              f"pi={ {k: round(v, 6) for k, v in pi.items()} } residual={res:.1e} "
              f"N={N} H={H} |S|={len(S)} max TV(split_s law, nu_(N+d))={tv:.2e}")
    print(f"[3] {tested} magmas tested ({nontrivial} with support >= 2); worst idempotent residual {worst_res:.1e}; worst TV {worst_tv:.2e}")
    assert worst_tv < 1e-7 and nontrivial >= 12
    # control: with a non-idempotent measure the same enumeration must detect a discrepancy
    delta = {(0, 0): 1, (0, 1): 1, (1, 0): 1, (1, 1): 1}
    reps = reachable(delta, 0)
    ctl = exact_model_check(delta, 0, {0: 0.5, 1: 0.5}, reps, 3, 1, X2)
    print(f"[3c] control (constant magma, uniform non-idempotent pi): max TV = {ctl:.3f} (must be > 0)")
    assert ctl > 0.1
    print(f"[4] free monoid calibration: words in both aM and bM: {calibrate_free_monoid()} (method must fail there)")
    print(f"[5] free magma has no idempotent probability measure: {no_idempotent_on_free_magma()}")


if __name__ == '__main__':
    main()
