#!/usr/bin/env python3
"""Fold-bootstrap seeding on finite quotients of F_2 = <a,b>.

Pair: K = <a, b a b^-2> <= L = F_2 (the Gamma_mal stage pair H_1 <= H_2).
For a finite quotient Q of L (images alpha, beta of a, b), the fold congruence
of the pullback Gamma_K x Cay(Q) is the 2-of-3 bootstrap closure on Q with
triples T_q = {q, q alpha^-1, q beta^-1}.  r(Q) = min number of seeds whose
closure is Q.  r(Q)/|Q| upper-bounds relC(R_L;R_K) for every profinite action
along a chain through Q (pulled-back closure is the closure of the pull-back).

We report: greedy upper bounds for r(Q), and the F_ell linear lower bound
dim ker(1 + lam*alpha^-1 + mu*beta^-1) on F_ell[Q] for small Q.
"""
import random
import sys
from collections import deque


# ---------- groups: PSL(2,p) as normalized 2x2 matrices ----------

def psl_norm(m, p):
    a, b, c, d = (x % p for x in m)
    # normalize sign: first nonzero entry in (a,b,c,d) is <= p//2
    for x in (a, b, c, d):
        if x:
            if x > p // 2:
                a, b, c, d = (-a) % p, (-b) % p, (-c) % p, (-d) % p
            break
    return (a, b, c, d)


def psl_mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return psl_norm((a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h), p)


def psl_random(p, rng):
    while True:
        a, b, c = rng.randrange(p), rng.randrange(p), rng.randrange(p)
        if a == 0:
            continue
        # d = (1 + b c) / a
        d = (1 + b * c) * pow(a, p - 2, p) % p
        return psl_norm((a, b, c, d), p)


def perm_mul(x, y):
    # right action convention: (x*y)(i) = y(x(i)), i.e. apply x first
    return tuple(y[i] for i in x)


def perm_random(n, rng):
    l = list(range(n))
    rng.shuffle(l)
    return tuple(l)


def enumerate_group(ident, gens, mul):
    """BFS by right multiplication.  Returns (elements, index, right tables)."""
    elts = [ident]
    idx = {ident: 0}
    tabs = [[] for _ in gens]
    dq = deque([0])
    # we fill tables in element order, so process sequentially
    i = 0
    while i < len(elts):
        x = elts[i]
        for k, g in enumerate(gens):
            y = mul(x, g)
            j = idx.get(y)
            if j is None:
                j = len(elts)
                idx[y] = j
                elts.append(y)
            tabs[k].append(j)
        i += 1
    return elts, idx, tabs


def inverse_table(t):
    inv = [0] * len(t)
    for i, j in enumerate(t):
        inv[j] = i
    return inv


# ---------- 2-of-3 bootstrap closure ----------

class Bootstrap:
    """Triples T_q = (q, ia[q], ib[q]).  Vertex v lies in T_v, T_{ra[v]}, T_{rb[v]}."""

    def __init__(self, ra, rb):
        self.n = n = len(ra)
        self.ra, self.rb = ra, rb
        ia, ib = inverse_table(ra), inverse_table(rb)
        self.tri = [(q, ia[q], ib[q]) for q in range(n)]
        self.reset()

    def reset(self):
        self.inS = bytearray(self.n)
        self.cnt = bytearray(self.n)
        self.size = 0
        self.ones = []  # lazy list of triples that reached count 1

    def triples_of(self, v):
        return (v, self.ra[v], self.rb[v])

    def add(self, v):
        """Add v and close.  Returns number of vertices added."""
        if self.inS[v]:
            return 0
        inS, cnt, tri = self.inS, self.cnt, self.tri
        dq = [v]
        inS[v] = 1
        added = 0
        while dq:
            u = dq.pop()
            added += 1
            for t in (u, self.ra[u], self.rb[u]):
                c = cnt[t] + 1
                cnt[t] = c
                if c == 1:
                    self.ones.append(t)
                elif c == 2:
                    for w in tri[t]:
                        if not inS[w]:
                            inS[w] = 1
                            dq.append(w)
        self.size += added
        return added

    def score(self, u):
        return sum(1 for t in self.triples_of(u) if self.cnt[t] == 1)

    def greedy(self, rng, smart=True):
        """Greedy seeding; returns number of seeds used to reach all of Q."""
        self.reset()
        n = self.n
        order = list(range(n))
        rng.shuffle(order)
        ptr = 0
        seeds = 0
        while self.size < n:
            v = None
            ones = self.ones
            while ones:
                k = rng.randrange(len(ones))
                t = ones[k]
                ones[k] = ones[-1]
                ones.pop()
                if self.cnt[t] == 1:
                    free = [w for w in self.tri[t] if not self.inS[w]]
                    if smart:
                        free.sort(key=self.score, reverse=True)
                    v = free[0]
                    break
            if v is None:
                while self.inS[order[ptr]]:
                    ptr += 1
                v = order[ptr]
            self.add(v)
            seeds += 1
        return seeds


# ---------- linear lower bound over F_2 ----------

def f2_kernel_dim(bs):
    """dim ker over F_2 of f -> f(q) + f(q a^-1) + f(q b^-1).

    If f is in the kernel and vanishes on two members of a triple, it vanishes
    on the third, so its zero set is closed; a seed set S with closure Q forces
    f = 0 from f|S = 0.  Hence r(Q) >= dim ker."""
    n = bs.n
    rows = []
    for (q, x, y) in bs.tri:
        r = (1 << q) ^ (1 << x) ^ (1 << y)
        rows.append(r)
    # Gaussian elimination with pivot = lowest set bit
    piv = {}
    rank = 0
    for r in rows:
        while r:
            lb = r & (-r)
            if lb in piv:
                r ^= piv[lb]
            else:
                piv[lb] = r
                rank += 1
                break
    return n - rank


# ---------- helpers ----------

def subgroup_order(ident, gens, mul, cap):
    seen = {ident}
    dq = [ident]
    while dq:
        x = dq.pop()
        for g in gens:
            y = mul(x, g)
            if y not in seen:
                seen.add(y)
                if len(seen) > cap:
                    return len(seen)
                dq.append(y)
    return len(seen)


def power(x, k, mul, ident):
    r = ident
    for _ in range(k):
        r = mul(r, x)
    return r


def inv_of(x, mul, ident):
    # brute: x^(ord-1)
    y = x
    prev = ident
    while y != ident:
        prev = y
        y = mul(y, x)
    return prev


def phi(y, alpha, mul, ident):
    """phi(y) = y alpha y^-2 (stage map b_{n+1} -> b_n)."""
    yi = inv_of(y, mul, ident)
    return mul(mul(mul(y, alpha), yi), yi)


def periodic_point(y, alpha, mul, ident, maxit=100000):
    seen = {}
    k = 0
    while y not in seen and k < maxit:
        seen[y] = k
        y = phi(y, alpha, mul, ident)
        k += 1
    return y, k - seen.get(y, k)  # a point on the cycle, and cycle length


# ---------- driver ----------

def run_group(label, ident, mul, rand, order, rng, trials, mal, f2cap):
    """Pick random generators alpha, beta; beta periodic under phi if mal."""
    for _attempt in range(200):
        alpha, beta = rand(), rand()
        cyc = 0
        if mal:
            beta, cyc = periodic_point(beta, alpha, mul, ident)
        gam = phi(beta, alpha, mul, ident)  # image of b_1 = b a b^-2
        if subgroup_order(ident, [alpha, beta], mul, order) != order:
            continue
        ksurj = subgroup_order(ident, [alpha, gam], mul, order) == order
        break
    else:
        print(label, "no generating pair found")
        return None
    elts, idx, (ra, rb) = enumerate_group(ident, [alpha, beta], mul)
    n = len(elts)
    assert n == order, (n, order)
    bs = Bootstrap(ra, rb)
    best = min(bs.greedy(rng, smart=True) for _ in range(trials))
    rnd = min(bs.greedy(rng, smart=False) for _ in range(max(1, trials // 2)))
    lb = f2_kernel_dim(bs) if n <= f2cap else None
    row = dict(group=label, n=n, mal_periodic=mal, cycle=cyc, K_surjects=ksurj,
               greedy_seeds=best, greedy_ratio=round(best / n, 5),
               random_seeds=rnd, f2_lower=lb)
    print(row, flush=True)
    return row


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 917)
    primes = [int(x) for x in (sys.argv[2].split(",") if len(sys.argv) > 2 else
                               "7,11,13,17,19,23,29,31".split(","))]
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    f2cap = int(sys.argv[4]) if len(sys.argv) > 4 else 7000
    rows = []
    for p in primes:
        order = p * (p * p - 1) // 2
        ident = (1, 0, 0, 1)
        mul = (lambda x, y, p=p: psl_mul(x, y, p))
        rand = (lambda p=p: psl_random(p, rng))
        for mal in (False, True):
            r = run_group("PSL2(%d)" % p, ident, mul, rand, order, rng, trials, mal, f2cap)
            if r:
                rows.append(r)
    for m in (5, 6, 7, 8):
        import math
        order = math.factorial(m)
        ident = tuple(range(m))
        rand = (lambda m=m: perm_random(m, rng))
        for mal in (False, True):
            r = run_group("S%d" % m, ident, perm_mul, rand, order, rng, trials, mal, f2cap)
            if r:
                rows.append(r)
    return rows


if __name__ == "__main__":
    main()
