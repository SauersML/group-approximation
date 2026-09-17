#!/usr/bin/env python3
"""Checks for thompson-f-degree-aware-automaton-flows-cannot-certify.

The theorem: no expansion certificate on Thompson's F is a function of s, the profile of a
finite tree automaton on the top forest, the number of trees and the total caret count
(degree). The proof builds a random forest ("pumped leaf model") whose statistic
Psi = (refined profile, N, total leaves) is approximately split-invariant.

This script checks, for several automata:
 1. Pump: with f = delta(leaf, .), preperiod j0 and period m, the trees V0 = c^j0(.) and
    V1 = c^(j0+m)(.) (c(T) = . ^ T) have the same refined state in Q x Z/m and m more leaves.
 2. An idempotent probability pi on R_V (refined states of trees containing V0).
 3. Brute force (N = 2, H = 2, s = x_1 and s = x_0): enumerate every forest of the model with its
    probability, apply split_s with real tree operations, and check that the law of
    (refined profile, N, degree) of split_s Y equals the product law predicted by the proof
    (independent positions, depth-k tops), exactly.
 4. Exact total variation between the Psi-law of split_s Y given N = n and the model law at
    N = n + d, for growing n, against the proof's bound 2 d 2^(H/2) Lmax / (m sqrt(n - d)).
 5. Control: without the coin (always T^0) the total variation does not decay.

Stdlib + numpy (single thread). Run:
  OMP_NUM_THREADS=1 nice -n 10 timeout 1200 python3 check_pumped_leaf_model.py
"""
import itertools, math, random
from collections import defaultdict
import numpy as np

LEAF = None


def leaves(t):
    return 1 if t is LEAF else leaves(t[0]) + leaves(t[1])


def carets(t):
    return 0 if t is LEAF else 1 + carets(t[0]) + carets(t[1])


class Automaton:
    def __init__(self, n, delta, leaf, name):
        self.n, self.delta, self.leaf, self.name = n, delta, leaf, name
        # f(q) = delta(leaf, q): preperiod j0 and period m on the orbit structure of Q
        f = [delta[(leaf, q)] for q in range(n)]
        seen = {}
        cur = tuple(range(n))
        j = 0
        while cur not in seen:
            seen[cur] = j
            cur = tuple(f[x] for x in cur)
            j += 1
        self.j0 = seen[cur]
        self.m = j - seen[cur]

    def q(self, t, memo={}):
        key = (id(self), t)
        if key in memo:
            return memo[key]
        v = self.leaf if t is LEAF else self.delta[(self.q(t[0]), self.q(t[1]))]
        memo[key] = v
        return v

    def rq(self, t):
        """refined state in Q x Z/m"""
        return (self.q(t), leaves(t) % self.m)

    def rdelta(self, a, b):
        return (self.delta[(a[0], b[0])], (a[1] + b[1]) % self.m)


def vine(j):
    t = LEAF
    for _ in range(j):
        t = (LEAF, t)
    return t


def contains(t, v):
    if t == v:
        return True
    return t is not LEAF and (contains(t[0], v) or contains(t[1], v))


def replace_first(t, v0, v1):
    """replace the first occurrence (preorder) of subtree v0 by v1; returns (tree, done)"""
    if t == v0:
        return v1, True
    if t is LEAF:
        return t, False
    l, done = replace_first(t[0], v0, v1)
    if done:
        return (l, t[1]), True
    r, done = replace_first(t[1], v0, v1)
    return (t[0], r), done


def representatives(A, rounds=6, cap=4000):
    """smallest found trees per refined state: all trees, and trees containing V0"""
    V0 = vine(A.j0)
    allrep = {A.rq(LEAF): LEAF}
    for _ in range(rounds):
        items = list(allrep.items())
        for (_, a), (_, b) in itertools.product(items, items):
            t = (a, b)
            s = A.rq(t)
            if s not in allrep or carets(t) < carets(allrep[s]):
                allrep[s] = t
    vrep = {A.rq(V0): V0}
    for _ in range(rounds):
        vit = list(vrep.items())
        ait = list(allrep.items())
        for (_, a), (_, b) in itertools.product(vit, ait):
            for t in ((a, b), (b, a)):
                s = A.rq(t)
                if s not in vrep or carets(t) < carets(vrep[s]):
                    vrep[s] = t
    return allrep, vrep


def idempotent(A, states, iters=4000):
    states = sorted(states)
    idx = {s: i for i, s in enumerate(states)}
    k = len(states)
    pi = np.full(k, 1.0 / k)
    for _ in range(iters):
        new = np.zeros(k)
        for i, a in enumerate(states):
            for j, b in enumerate(states):
                new[idx[A.rdelta(a, b)]] += pi[i] * pi[j]
        pi = 0.5 * pi + 0.5 * new
        pi = pi / pi.sum()  # the fixed point sum = 1 of s -> (s + s^2)/2 is unstable in floating point
    new = np.zeros(k)
    for i, a in enumerate(states):
        for j, b in enumerate(states):
            new[idx[A.rdelta(a, b)]] += pi[i] * pi[j]
    res = float(np.abs(new - pi).max())
    return {s: float(pi[i]) for i, s in enumerate(states) if pi[i] > 1e-12}, res


def hung_trees(A, vrep, pi, coin=True):
    V0, V1 = vine(A.j0), vine(A.j0 + A.m)
    out = []  # (tree, refined state, prob)
    for r, p in pi.items():
        T0 = vrep[r]
        T1, done = replace_first(T0, V0, V1)
        assert done and A.rq(T1) == r and leaves(T1) == leaves(T0) + A.m
        if coin:
            out += [(T0, r, p / 2), (T1, r, p / 2)]
        else:
            out += [(T0, r, p)]
    return out


def top_laws(A, hung, H):
    """law[h] = dict (refined state, leaves) -> prob, for a complete depth-h top over hung trees"""
    law = [defaultdict(float)]
    for t, r, p in hung:
        law[0][(r, leaves(t))] += p
    for h in range(H):
        nl = defaultdict(float)
        for (a, la), pa in law[h].items():
            for (b, lb), pb in law[h].items():
                nl[(A.rdelta(a, b), la + lb)] += pa * pb
        law.append(nl)
    return law


def split_depths(word, N):
    """depths of the antichain nodes after split_(i_d) ... split_(i_1)"""
    dep = [0] * N
    for i in word:
        k = dep[i]
        dep[i:i + 1] = [k + 1, k + 1]
    return dep


def strip(f):
    f = list(f)
    while f and f[-1] is LEAF:
        f.pop()
    return tuple(f)


def split(k, f):
    f = list(f)
    if k >= len(f) or f[k] is LEAF:
        return None
    L, R = f[k]
    return strip(f[:k] + [L, R] + f[k + 1:])


def complete_top(h, subtrees):
    level = list(subtrees)
    for _ in range(h):
        level = [(level[2 * i], level[2 * i + 1]) for i in range(len(level) // 2)]
    return level[0]


def brute_force_check(A, hung, H, N, word):
    d = len(word)
    law_split = defaultdict(float)
    B = 2 ** H
    for combo in itertools.product(range(len(hung)), repeat=N * B):
        p = 1.0
        for c in combo:
            p *= hung[c][2]
        forest = strip([complete_top(H, [hung[c][0] for c in combo[a * B:(a + 1) * B]]) for a in range(N)])
        z = forest
        for i in word:
            z = split(i, z)
            assert z is not None
        prof = tuple(A.rq(t) for t in z)
        Nz = len(z)
        deg = sum(carets(t) for t in z)
        assert Nz == N + d and deg == sum(carets(t) for t in forest) - d
        law_split[(prof, Nz, deg)] += p
    # predicted: independent positions, depth-k tops
    tl = top_laws(A, hung, H)
    dep = split_depths(word, N)
    pred = {((), 0): 1.0}
    for k in dep:
        new = defaultdict(float)
        for (prof, L), p in pred.items():
            for (r, l), q in tl[H - k].items():
                new[(prof + (r,), L + l)] += p * q
        pred = new
    pred2 = defaultdict(float)
    for (prof, L), p in pred.items():
        pred2[(prof, N + d, L - (N + d))] += p  # degree = leaves - number of trees
    keys = set(law_split) | set(pred2)
    return max(abs(law_split.get(k, 0) - pred2.get(k, 0)) for k in keys), len(keys)


def exact_tv(A, hung, H, n, word):
    """TV between (refined profile, N, degree) of split_s Y given N = n and the model at n + d."""
    d = len(word)
    tl = top_laws(A, hung, H)
    dep = split_depths(word, n)
    states = sorted({r for (r, _) in tl[0]})
    maxlen = n * (2 ** H) * max(l for (_, l) in tl[0]) + (2 ** H) * d * max(l for (_, l) in tl[0]) + 2

    def arr(law, r):
        a = np.zeros(max(l for (_, l) in law) + 1)
        for (s, l), p in law.items():
            if s == r:
                a[l] += p
        return a

    P = {(k, r): arr(tl[H - k], r) for k in set(dep) | {0} for r in states}
    J = [a for a, k in enumerate(dep) if k > 0]
    nroot = len(dep) - len(J)
    # powers of root laws
    pw = {r: [np.array([1.0])] for r in states}
    for r in states:
        for _ in range(nroot):
            pw[r].append(np.convolve(pw[r][-1], P[(0, r)]))
    tv = 0.0
    for c in itertools.product(range(nroot + 1), repeat=len(states) - 1):
        if sum(c) > nroot:
            continue
        cnt = list(c) + [nroot - sum(c)]
        mult = math.factorial(nroot)
        for x in cnt:
            mult //= math.factorial(x)
        Ac = np.array([1.0])
        for r, x in zip(states, cnt):
            Ac = np.convolve(Ac, pw[r][x])
        for xiJ in itertools.product(states, repeat=len(J)):
            Bs, Bm = np.array([1.0]), np.array([1.0])
            for a, r in zip(J, xiJ):
                Bs = np.convolve(Bs, P[(dep[a], r)])
                Bm = np.convolve(Bm, P[(0, r)])
            L = max(len(Bs), len(Bm))
            diff = np.zeros(L)
            diff[:len(Bs)] += Bs
            diff[:len(Bm)] -= Bm
            tv += 0.5 * mult * np.abs(np.convolve(Ac, diff)).sum()
    Lmax = max(l for (_, l) in tl[0])
    bound = 2 * d * 2 ** (H / 2) * Lmax / (A.m * math.sqrt(n - d))
    return tv, bound


def parity_automaton():
    delta = {(a, b): (a + b) % 2 for a in range(2) for b in range(2)}
    return Automaton(2, delta, 1, "leaves mod 2")


def depth_trunc_automaton():
    # state = min(depth, 2)
    delta = {(a, b): min(2, 1 + max(a, b)) for a in range(3) for b in range(3)}
    return Automaton(3, delta, 0, "depth truncated at 2")


def right_vine_automaton():
    # state 0: leaf; 1: . ^ leaf-or-1 chain (right vine); 2: anything else
    delta = {}
    for a in range(3):
        for b in range(3):
            delta[(a, b)] = 1 if (a == 0 and b in (0, 1)) else 2
    return Automaton(3, delta, 0, "is a right vine")


def main():
    rng = random.Random(20260917)
    autos = [parity_automaton(), depth_trunc_automaton(), right_vine_automaton()]
    for _ in range(40):
        n = rng.choice([2, 3])
        delta = {(a, b): rng.randrange(n) for a in range(n) for b in range(n)}
        autos.append(Automaton(n, delta, rng.randrange(n), "random %d-state" % n))
    done_rand = 0
    print("== 1-2. pump and idempotent measure ==")
    usable = []
    for A in autos:
        allrep, vrep = representatives(A)
        pi, res = idempotent(A, vrep.keys())
        V0, V1 = vine(A.j0), vine(A.j0 + A.m)
        assert A.rq(V0) == A.rq(V1) and leaves(V1) == leaves(V0) + A.m
        closed = all(A.rdelta(a, b) in vrep for a in vrep for b in allrep) and \
            all(A.rdelta(b, a) in vrep for a in vrep for b in allrep)
        if not closed or not (res <= 1e-10) or len(pi) > 3:
            continue
        if A.name.startswith("random"):
            if len(pi) < 2 or done_rand >= 3:
                continue
            done_rand += 1
        usable.append((A, vrep, pi))
        print("%-22s |Q|=%d j0=%d m=%d |R_V|=%d supp(pi)=%d residual=%.1e pi=%s" % (
            A.name, A.n, A.j0, A.m, len(vrep), len(pi), res,
            {k: round(v, 4) for k, v in pi.items()}))
    print("\n== 3. brute force vs predicted product law (N=2, H=2) ==")
    for A, vrep, pi in usable[:3]:
        hung = hung_trees(A, vrep, pi)
        if len(hung) > 4:
            print("%-22s skipped (|hung|=%d)" % (A.name, len(hung)))
            continue
        for word in [(1,), (0,)]:
            err, nk = brute_force_check(A, hung, 2, 2, word)
            print("%-22s s=x_%d  max |law difference| = %.2e over %d atoms" % (A.name, word[0], err, nk))
            assert err < 1e-12
    print("\n== 4. exact TV of Psi-laws, split_s Y (N=n) vs model (N=n+d) ==")
    for A, vrep, pi in usable:
        hung = hung_trees(A, vrep, pi)
        for word, H in [((1,), 2), ((0, 2), 3)]:
            row = []
            ns = [4, 8, 16, 32, 64] if H == 2 else [4, 8, 16, 32]
            if len(pi) == 1:
                ns += [128, 256, 512] if H == 2 else [64, 128]
            for n in ns:
                tv, bound = exact_tv(A, hung, H, n, word)
                assert tv <= bound + 1e-9
                row.append("n=%d tv=%.4f (sqrt(n)tv=%.3f, bound %.2f)" % (n, tv, math.sqrt(n) * tv, bound))
            print("%-22s s=%s H=%d: %s" % (A.name, "x_" + "x_".join(map(str, word)), H, "; ".join(row)))
    print("\n== 5. control: no coin (always T^0) ==")
    for A, vrep, pi in usable[:3]:
        hung = hung_trees(A, vrep, pi, coin=False)
        row = []
        for n in [4, 16, 64]:
            tv, _ = exact_tv(A, hung, 2, n, (1,))
            row.append("n=%d tv=%.4f" % (n, tv))
        print("%-22s s=x_1: %s" % (A.name, "; ".join(row)))
    print("\nall checks passed")


if __name__ == "__main__":
    main()
