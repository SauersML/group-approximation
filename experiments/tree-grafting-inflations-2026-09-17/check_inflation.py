"""Sanity checks for research/tree-grafting-inflations-kill-superlinear-ratio-derivatives.md.

Trees are frozensets of binary strings (the leaves, a complete prefix code).
Generators of F act by prefix replacement (Moore, arXiv:0905.1118v7, Sec. 4).

Checks:
 1. one-sided equivariance sigma(T.g) = sigma(T).g for leaf-grafting inflations;
 2. the Inflation Lemma bd(sigma_* mu) <= 2 bd(mu) on random measures;
 3. for S = delta^{j(n)} T with phi(x) = max(2x, x^2): no U dominated by S that
    splits root, 0, 1, 10 (so that U.x0, U.x1 are defined) satisfies the phi-chain
    condition on consecutive interior leaves, in either direction;
 4. for comparison, Moore's phi(x) = 2x on the same S.
"""
import random
from functools import lru_cache

X0 = [("00", "0"), ("01", "10"), ("1", "11")]
X1 = [("0", "0"), ("100", "10"), ("101", "110"), ("11", "111")]
inv = lambda g: [(t, s) for (s, t) in g]
GENS = {"x0": X0, "x0i": inv(X0), "x1": X1, "x1i": inv(X1)}
INV = {"x0": "x0i", "x0i": "x0", "x1": "x1i", "x1i": "x1"}


def act(T, g):
    out = []
    for u in T:
        for s, t in g:
            if u.startswith(s):
                out.append(t + u[len(s):])
                break
        else:
            return None
    return frozenset(out)


def trees(n, prefix=""):
    if n == 1:
        yield frozenset([prefix])
        return
    for k in range(1, n):
        for L in trees(k, prefix + "0"):
            for R in trees(n - k, prefix + "1"):
                yield L | R


def delta(T, j):
    if j == 0:
        return T
    ws = [format(i, "0%db" % j) for i in range(2 ** j)]
    return frozenset(u + w for u in T for w in ws)


def sigma_factory(jfun):
    return lambda T: delta(T, jfun(len(T)))


def graft_kth(P, k):
    """graft the fixed tree P (leaves as strings, root '') at the k-th leaf from the left"""
    def s(T):
        L = sorted(T)
        if k >= len(L):
            return T
        return frozenset(L[:k] + [L[k] + p for p in P] + L[k + 1:])
    return s


def check_equivariance(sigma, nmax=6):
    bad = 0
    tot = 0
    for n in range(1, nmax + 1):
        for T in trees(n):
            for g in GENS.values():
                Tg = act(T, g)
                if Tg is None:
                    continue
                tot += 1
                if act(sigma(T), g) != sigma(Tg):
                    bad += 1
    return tot, bad


def bd(mu):
    total = 0.0
    for gname, g in GENS.items():
        gi = GENS[INV[gname]]
        cand = set(mu)
        for t in mu:
            s = act(t, gi)
            if s is not None:
                cand.add(s)
        for s in cand:
            sg = act(s, g)
            total += abs((mu.get(sg, 0.0) if sg is not None else 0.0) - mu.get(s, 0.0))
    return total


def push(sigma, mu):
    nu = {}
    for T, w in mu.items():
        s = sigma(T)
        nu[s] = nu.get(s, 0.0) + w
    return nu


def check_inflation_lemma(sigma, trials=300, nmax=6, seed=1):
    rng = random.Random(seed)
    alltrees = [T for n in range(1, nmax + 1) for T in trees(n)]
    worst = 0.0
    for _ in range(trials):
        supp = rng.sample(alltrees, rng.randint(1, 40))
        mu = {T: rng.random() for T in supp}
        b = bd(mu)
        nb = bd(push(sigma, mu))
        if b > 0:
            worst = max(worst, nb / b)
        assert nb <= 2 * b + 1e-9, (nb, b)
    return worst


# ---------- chain DP on S -------------------------------------------------
def subtree_sizes(S):
    size = {}
    for u in S:
        for d in range(len(u) + 1):
            size[u[:d]] = size.get(u[:d], 0) + 1
    return size


def chain_exists(S, cond):
    """Is there U dominated by S, splitting '', '0', '1', '10', whose interior leaves
    (all but min and max) satisfy cond(|S/u|, |S/v|) for consecutive u < v?"""
    size = subtree_sizes(S)
    leafset = set(S)
    memo = {}

    def F(x):  # set of (first, last) of valid chains for codes of S/x
        if ("F", x) in memo:
            return memo[("F", x)]
        res = {(size[x], size[x])}
        if x not in leafset:
            for f1, l1 in F(x + "0"):
                for f2, l2 in F(x + "1"):
                    if cond(l1, f2):
                        res.add((f1, l2))
        memo[("F", x)] = res
        return res

    def DF(x):  # drop first leaf: set of last values (None = empty)
        if ("DF", x) in memo:
            return memo[("DF", x)]
        res = {None}
        if x not in leafset:
            for a in DF(x + "0"):
                for f2, l2 in F(x + "1"):
                    if a is None or cond(a, f2):
                        res.add(l2)
        memo[("DF", x)] = res
        return res

    def DL(x):  # drop last leaf: set of first values (None = empty)
        if ("DL", x) in memo:
            return memo[("DL", x)]
        res = {None}
        if x not in leafset:
            for f1, l1 in F(x + "0"):
                for b in DL(x + "1"):
                    if b is None or cond(l1, b):
                        res.add(f1)
        memo[("DL", x)] = res
        return res

    for need in ["", "0", "1", "10"]:
        if need in leafset:
            return False
    for a in DF("00"):
        for f1, l1 in F("01"):
            if a is not None and not cond(a, f1):
                continue
            for f2, l2 in F("100"):
                if not cond(l1, f2):
                    continue
                for f3, l3 in F("101"):
                    if not cond(l2, f3):
                        continue
                    for b in DL("11"):
                        if b is None or cond(l3, b):
                            return True
    return False


def both_dirs(S, phi):
    inc = chain_exists(S, lambda u, v: v >= phi(u))
    dec = chain_exists(S, lambda u, v: u >= phi(v))
    return inc or dec


def jfun_for(phi):
    def j(n):
        jj = 3
        while not phi(2 ** (jj - 3)) > 2 ** jj * n:
            jj += 1
        return jj
    return j


if __name__ == "__main__":
    # 1. equivariance
    for name, sig in [("delta^1", sigma_factory(lambda n: 1)),
                      ("delta^{n}", sigma_factory(lambda n: n)),
                      ("delta^{n mod 3} (non-monotone)", sigma_factory(lambda n: n % 3)),
                      ("graft 01-cherry at leaf 1", graft_kth(["0", "1"], 1))]:
        print("equivariance", name, check_equivariance(sig))
    # 2. inflation lemma
    for name, sig in [("delta^{n}", sigma_factory(lambda n: n)),
                      ("delta^{n mod 3}", sigma_factory(lambda n: n % 3))]:
        print("inflation lemma worst ratio bd(nu)/bd(mu)", name, round(check_inflation_lemma(sig), 4))
    # 3. superlinear phi kills
    phi_sq = lambda x: max(2 * x, x * x)
    jsq = jfun_for(phi_sq)
    for n in range(1, 6):
        ts = list(trees(n))
        hits = sum(both_dirs(delta(T, jsq(n)), phi_sq) for T in ts)
        print("phi=max(2x,x^2) n=%d j=%d trees=%d with-U=%d" % (n, jsq(n), len(ts), hits))
    # 4. Moore's linear phi on inflated trees
    phi_lin = lambda x: 2 * x
    for n in range(1, 6):
        for j in (3, 5, 7):
            ts = list(trees(n))
            hits = sum(both_dirs(delta(T, j), phi_lin) for T in ts)
            print("phi=2x n=%d j=%d trees=%d with-U=%d" % (n, j, len(ts), hits))
