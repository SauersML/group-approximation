"""Checks for transition-digraph-capacity-lifts-give-nonsurjunctive-sizes.

Part 1 (arithmetic). For b, z >= 1 with d = gcd(b, z), b = d b', z = d z', the set
{b m + z s : m >= 1, 1 <= s <= m} contains every d n' with n' >= b'(b' + z').
If d is a power of two, the set contains a power of two. Example (3, 7) gives 64.

Part 2 (construction). Over the cyclic groups Z/N (as a finite sanity model), for random
local rules tau on A = {0..k-1} with memory M = {0, 1}, compute the transition relation
R = {(x(g), tau(x)(g))}, pick capacities n monotone along R, build the label lift Phi, and
check r o Phi = tau o r, and that Phi is injective exactly when tau is. It also checks
that each upset of R is sitewise absorbing and that the class-size gcd equals the gcd of
upset sizes.
"""
import itertools
import math
import random


def sizes(b, z, bound):
    out = set()
    for m in range(1, bound + 1):
        for s in range(1, m + 1):
            v = b * m + z * s
            if v <= bound:
                out.add(v)
    return out


def part1():
    bound = 1200
    for b in range(1, 16):
        for z in range(1, 16):
            d = math.gcd(b, z)
            bp, zp = b // d, z // d
            S = sizes(b, z, bound)
            start = d * bp * (bp + zp)
            for v in range(start, bound + 1, d):
                assert v in S, (b, z, v)
            assert all(v % d == 0 for v in S)
            if d & (d - 1) == 0:
                assert any(v & (v - 1) == 0 for v in S), (b, z)
    assert 64 in sizes(3, 7, 200)
    assert 7 * 7 + 3 * 5 == 64
    print("part1 ok")


def closure_classes(k, R):
    reach = [[i == j or (i, j) in R for j in range(k)] for i in range(k)]
    for t in range(k):
        for i in range(k):
            for j in range(k):
                if reach[i][t] and reach[t][j]:
                    reach[i][j] = True
    classes = []
    seen = set()
    for i in range(k):
        if i in seen:
            continue
        c = [j for j in range(k) if reach[i][j] and reach[j][i]]
        seen.update(c)
        classes.append(c)
    return reach, classes


def part2(trials=150, N=4, k=3):
    rng = random.Random(20260917)
    configs = list(itertools.product(range(k), repeat=N))
    n_inj = 0
    for _ in range(trials):
        rule = {u: rng.randrange(k) for u in itertools.product(range(k), repeat=2)}
        mode = rng.randrange(3)
        if mode:
            pi = list(range(k))
            rng.shuffle(pi)
            # mode 1: sitewise permutation (cycles as classes); mode 2: shift then permute
            rule = {u: pi[u[mode - 1]] for u in rule}

        def tau(x):
            return tuple(rule[(x[g], x[(g + 1) % N])] for g in range(N))

        R = {(u[0], rule[u]) for u in rule}
        reach, classes = closure_classes(k, R)
        upsets = []
        for mask in range(1, 2 ** k):
            U = [a for a in range(k) if mask >> a & 1]
            if all(b in U for a in U for b in range(k) if reach[a][b]):
                upsets.append(U)
                for x in configs:
                    y = tau(x)
                    assert all(y[g] in U for g in range(N) if x[g] in U)
        g_classes = math.gcd(*[len(c) for c in classes])
        g_upsets = math.gcd(*[len(U) for U in upsets])
        assert g_classes == g_upsets, (classes, upsets)
        # random monotone capacity: 1 + sum of random multiples of upset indicators
        cap = [1] * k
        for U in rng.sample(upsets, min(2, len(upsets))):
            c = rng.randrange(2)
            for a in U:
                cap[a] += c
        for (a, b) in R:
            assert cap[a] <= cap[b]
        B = [(a, i) for a in range(k) for i in range(cap[a])]
        lifts = list(itertools.product(B, repeat=N))

        def phi(y):
            x = tuple(p[0] for p in y)
            tx = tau(x)
            return tuple((tx[g], y[g][1]) for g in range(N))

        images = set()
        for y in lifts:
            w = phi(y)
            assert all(w[g][1] < cap[w[g][0]] for g in range(N))
            assert tuple(p[0] for p in w) == tau(tuple(p[0] for p in y))
            images.add(w)
        tau_inj = len({tau(x) for x in configs}) == len(configs)
        phi_inj = len(images) == len(lifts)
        assert tau_inj == phi_inj
        n_inj += tau_inj
    print("part2 ok", trials, "rules,", n_inj, "injective")


if __name__ == "__main__":
    part1()
    part2()
