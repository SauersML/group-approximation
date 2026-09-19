#!/usr/bin/env python3
"""Numeric checks of the Bafna--Minzer steps that touch the alphabet, over
non-abelian groups (S_3, Q_8), with exact rational arithmetic.

Games: left-shift games x_v = b_e x_u on the complete graph K_n (n=4).
Distributions: explicit (real) distributions mu on labelings V -> A.
These are a special case of pseudodistributions, so this checks the algebra
of each step, not the SoS degree bookkeeping.

C1  Psi(mu) = Psi(mu^sym)          (BM rounding.tex, "We note that Psi(mu) = Psi(mu^sym)")
C2  Condition&Round >= Psi(mu^sym) (BBKSS Lemma 3.6 / BM Lemma 3.29)
C3  Phi(mu1 x mu2) = Phi(mu1^sym x mu2^sym) and Phi invariant under X->Xt, X'->X't'
C4  lem:relating-ent-j (BM low-comp.tex) with nu = 0 and exact threshold
    p = 1[val >= beta]:  Phi(mu1 x mu2 | E) <= Psi(mu1)/(2 beta^2)
    + Psi(mu2)/(2 beta^2) + 2 delta + 1/|V|   (zeta = 0, delta = max TV of
    local tuples Y_{uv} under the conditioned vs product measure)
C5  Fact 2.10(3): an edge crossing two parts of the shift partition is
    violated by X or X' (checked on all labelings of the edge)
C6  Claim A.4: randomized constraints are satisfied w.p. exactly 1/|A|
C7  control: with the wrong-sided difference X_u X'_u^{-1}, C5 fails for S_3
"""
import itertools
import random
from fractions import Fraction as Fr


# ---------------------------------------------------------------- groups
def make_S3():
    elems = list(itertools.permutations(range(3)))
    def mul(p, q):  # (p*q)(i) = p(q(i))
        return tuple(p[q[i]] for i in range(3))
    return "S3", elems, mul


def make_Q8():
    # elements (sign, unit) with unit in 1,i,j,k
    table = {("1", "1"): (1, "1"), ("1", "i"): (1, "i"), ("1", "j"): (1, "j"), ("1", "k"): (1, "k"),
             ("i", "1"): (1, "i"), ("i", "i"): (-1, "1"), ("i", "j"): (1, "k"), ("i", "k"): (-1, "j"),
             ("j", "1"): (1, "j"), ("j", "i"): (-1, "k"), ("j", "j"): (-1, "1"), ("j", "k"): (1, "i"),
             ("k", "1"): (1, "k"), ("k", "i"): (1, "j"), ("k", "j"): (-1, "i"), ("k", "k"): (-1, "1")}
    elems = [(s, u) for s in (1, -1) for u in "1ijk"]
    def mul(x, y):
        sg, un = table[(x[1], y[1])]
        return (x[0] * y[0] * sg, un)
    return "Q8", elems, mul


class Group:
    def __init__(self, spec):
        self.name, self.elems, self.mul = spec
        self.e = [g for g in self.elems if all(self.mul(g, h) == h for h in self.elems)][0]
        self._inv = {g: [h for h in self.elems if self.mul(g, h) == self.e][0] for g in self.elems}
        assert any(self.mul(g, h) != self.mul(h, g) for g in self.elems for h in self.elems)

    def inv(self, g):
        return self._inv[g]


# ---------------------------------------------------------------- games
class Game:
    """Left-shift game x_w = b[(v,w)] x_v on the complete graph K_n."""
    def __init__(self, G, n, rng, planted=None):
        self.G, self.n = G, n
        self.V = list(range(n))
        self.b = {}
        for v in self.V:
            for w in self.V:
                if v < w:
                    if planted is not None and rng.random() < 0.75:
                        bb = G.mul(planted[w], G.inv(planted[v]))  # satisfied by planted
                    else:
                        bb = rng.choice(G.elems)
                    self.b[(v, w)] = bb
                    self.b[(w, v)] = G.inv(bb)
        # sanity: x_w = b x_v  <=>  x_v = b^-1 x_w
        for (v, w), bb in self.b.items():
            assert self.b[(w, v)] == G.inv(bb)

    def sat(self, x, v, w):
        return x[w] == self.G.mul(self.b[(v, w)], x[v])

    def val_v(self, x, v):
        return Fr(sum(1 for w in self.V if w != v and self.sat(x, v, w)), self.n - 1)

    def value(self, x):
        return sum((self.val_v(x, v) for v in self.V), Fr(0)) / self.n


# ------------------------------------------------------------ distributions
def normalize(mu):
    tot = sum(mu.values())
    return {x: w / tot for x, w in mu.items() if w != 0}


def random_mu(game, rng, planted, m=30):
    G, n = game.G, game.n
    mu = {}
    for _ in range(m):
        if rng.random() < 0.5:
            t = rng.choice(G.elems)
            x = [G.mul(planted[v], t) for v in game.V]
            for v in game.V:
                if rng.random() < 0.25:
                    x[v] = rng.choice(G.elems)
        else:
            x = [rng.choice(G.elems) for _ in game.V]
        x = tuple(x)
        mu[x] = mu.get(x, 0) + Fr(rng.randint(1, 9))
    return normalize(mu)


def right_translate(mu, G, t):
    out = {}
    for x, w in mu.items():
        y = tuple(G.mul(a, t) for a in x)
        out[y] = out.get(y, 0) + w
    return out


def symmetrize(mu, G):
    out = {}
    for t in G.elems:
        for y, w in right_translate(mu, G, t).items():
            out[y] = out.get(y, 0) + w / len(G.elems)
    return out


def rq(G, xv, xu):
    """right quotient X_v X_u^{-1}"""
    return G.mul(xv, G.inv(xu))


# ------------------------------------------------------------ potentials
def Psi(mu, game):
    """E_{u,v} sum_s Pr[X_v X_u^-1 = s]^2 E[val_v | X_v X_u^-1 = s]
       = E_{u,v} sum_s Pr[s] * E[val_v 1[s]]  (u, v independent uniform)."""
    G, V = game.G, game.V
    tot = Fr(0)
    for u in V:
        for v in V:
            P = {s: Fr(0) for s in G.elems}
            Q = {s: Fr(0) for s in G.elems}
            for x, w in mu.items():
                s = rq(G, x[v], x[u])
                P[s] += w
                Q[s] += w * game.val_v(x, v)
            tot += sum(P[s] * Q[s] for s in G.elems)
    return tot / (len(V) ** 2)


def condition_and_round(mu, game):
    """E_u [ expected value of independent rounding of mu | X_u = e ]."""
    G, V = game.G, game.V
    tot = Fr(0)
    for u in V:
        cond = normalize({x: w for x, w in mu.items() if x[u] == G.e})
        marg = {v: {a: Fr(0) for a in G.elems} for v in V}
        for x, w in cond.items():
            for v in V:
                marg[v][x[v]] += w
        val = Fr(0)
        for v in V:
            for w_ in V:
                if w_ == v:
                    continue
                bb = game.b[(v, w_)]
                val += sum(marg[v][s] * marg[w_][G.mul(bb, s)] for s in G.elems)
        tot += val / (len(V) * (len(V) - 1))
    return tot / len(V)


def Phi_pair(x, xp, game, beta):
    """sum_s (E_u Z_{u,s} p_u p'_u)^2 with Z_{u,s} = [X_u^{-1} X'_u = s], p = 1[val >= beta]."""
    G, V = game.G, game.V
    acc = {s: Fr(0) for s in G.elems}
    for u in V:
        if game.val_v(x, u) >= beta and game.val_v(xp, u) >= beta:
            acc[G.mul(G.inv(x[u]), xp[u])] += Fr(1, len(V))
    return sum(a * a for a in acc.values())


def Phi(D, game, beta):
    return sum(w * Phi_pair(x, xp, game, beta) for (x, xp), w in D.items())


def product(mu1, mu2):
    return {(x, xp): w1 * w2 for x, w1 in mu1.items() for xp, w2 in mu2.items()}


def local_tuple(x, xp, u, v, game, beta):
    return (x[u], x[v], game.val_v(x, u) >= beta, game.val_v(x, v) >= beta,
            xp[u], xp[v], game.val_v(xp, u) >= beta, game.val_v(xp, v) >= beta)


def tv_local(D1, D2, u, v, game, beta):
    P, Q = {}, {}
    for (x, xp), w in D1.items():
        k = local_tuple(x, xp, u, v, game, beta)
        P[k] = P.get(k, 0) + w
    for (x, xp), w in D2.items():
        k = local_tuple(x, xp, u, v, game, beta)
        Q[k] = Q.get(k, 0) + w
    keys = set(P) | set(Q)
    return sum(abs(P.get(k, 0) - Q.get(k, 0)) for k in keys) / 2


# ------------------------------------------------------------ checks
def keep_min(worst, key, val):
    worst[key] = val if worst[key] is None else min(worst[key], val)


def run(spec, seed, trials, n=4):
    G = Group(spec)
    rng = random.Random(seed)
    beta = Fr(2, 3)
    worst = {k: None for k in ("C2_slack", "C4_slack", "C4main_slack")}
    maxPhi = Fr(0)
    for tr in range(trials):
        planted = [rng.choice(G.elems) for _ in range(n)]
        game = Game(G, n, rng, planted)
        mu1 = random_mu(game, rng, planted)
        mu2 = random_mu(game, rng, planted)
        s1, s2 = symmetrize(mu1, G), symmetrize(mu2, G)
        # C1  Psi(mu) = Psi(mu^sym)
        P1, P2 = Psi(mu1, game), Psi(mu2, game)
        assert P1 == Psi(s1, game) and P2 == Psi(s2, game), "C1"
        # C2  Condition&Round on mu^sym >= Psi(mu^sym)
        for s, P in ((s1, P1), (s2, P2)):
            slack = condition_and_round(s, game) - P
            assert slack >= 0, "C2"
            keep_min(worst, "C2_slack", slack)
        # C3  Phi invariance
        prod = product(mu1, mu2)
        ph = Phi(prod, game, beta)
        assert ph == Phi(product(s1, s2), game, beta), "C3 sym"
        t, tp = rng.choice(G.elems), rng.choice(G.elems)
        assert ph == Phi(product(right_translate(mu1, G, t), right_translate(mu2, G, tp)), game, beta), "C3 t"
        # C4  lem:relating-ent-j, nu = 0, exact threshold
        D = normalize({k: w * Fr(rng.randint(0, 4), 4) for k, w in prod.items()})
        phD = Phi(D, game, beta)
        maxPhi = max(maxPhi, phD)
        delta = max(tv_local(D, prod, u, v, game, beta)
                    for u in game.V for v in game.V if u != v)
        # the expansion (BM rounding.tex eq. relating-potential) in group form:
        # sum_s Z_{u,s} Z_{v,s} = [X_v X_u^-1 = X'_v X'_u^-1]   (Lemma D item 5)
        tot = Fr(0)
        for (x, xp), w in D.items():
            for u in game.V:
                for v in game.V:
                    if (rq(G, x[v], x[u]) == rq(G, xp[v], xp[u]) and
                            all(game.val_v(y, z) >= beta for y in (x, xp) for z in (u, v))):
                        tot += w
        assert tot / n ** 2 == phD, "C4 expansion"
        # main term split over s (BM, 'Bounding the main term'), group form
        main = Fr(0)
        for u in game.V:
            for v in game.V:
                A1 = {s: Fr(0) for s in G.elems}
                A2 = {s: Fr(0) for s in G.elems}
                for mu, Acc in ((mu1, A1), (mu2, A2)):
                    for x, w in mu.items():
                        if game.val_v(x, u) >= beta and game.val_v(x, v) >= beta:
                            Acc[rq(G, x[v], x[u])] += w
                main += sum(A1[s] * A2[s] for s in G.elems)
        main /= n ** 2
        assert main == ph, "C4 main = Phi(mu1 x mu2)"
        mslack = (P1 + P2) / (2 * beta ** 2) - main
        assert mslack >= 0, "C4 main bound"
        bound = (P1 + P2) / (2 * beta ** 2) + 2 * delta + Fr(1, n)
        assert bound - phD >= 0, "C4"
        keep_min(worst, "C4_slack", bound - phD)
        keep_min(worst, "C4main_slack", mslack)
    return G, worst, maxPhi


def edge_checks(spec):
    G = Group(spec)
    A = G.elems
    c5 = c6 = c7_fail = 0
    for bb in A:
        for xu, xpu in itertools.product(A, A):
            xv, xpv = G.mul(bb, xu), G.mul(bb, xpu)   # edge satisfied by X and X'
            # C5: shift-partition index X_u^{-1} X'_u agrees on both endpoints
            assert G.mul(G.inv(xu), xpu) == G.mul(G.inv(xv), xpv), "C5"
            c5 += 1
            # C7 control: wrong-sided X'_u X_u^{-1}
            if G.mul(xpu, G.inv(xu)) != G.mul(xpv, G.inv(xv)):
                c7_fail += 1
    # C6: each fixed (x_u, x_v) satisfied by exactly one b, i.e. prob 1/|A|
    for xu, xv in itertools.product(A, A):
        assert sum(1 for bb in A if G.mul(bb, xu) == xv) == 1, "C6"
        c6 += 1
    # item 5 over the whole group, and its wrong-sided failure
    i5 = i5wrong = 0
    for xu, xpu, xv, xpv in itertools.product(A, A, A, A):
        lhs = G.mul(G.inv(xu), xpu) == G.mul(G.inv(xv), xpv)
        rhs = rq(G, xv, xu) == rq(G, xpv, xpu)
        assert lhs == rhs, "item 5"
        i5 += 1
        if lhs != (G.mul(xpu, G.inv(xu)) == G.mul(xpv, G.inv(xv))):
            i5wrong += 1
    return c5, c6, c7_fail, i5, i5wrong


def main():
    for spec, seed in ((make_S3(), 1), (make_Q8(), 2)):
        name = spec[0]
        c5, c6, c7, i5, i5w = edge_checks(spec)
        print(f"[{name}] C5 crossing-edge fact: {c5} satisfied (b, X_u, X'_u) triples, all agree  OK")
        print(f"[{name}] C6 randomized constraint prob 1/|A|: {c6} (x_u, x_v) pairs  OK")
        print(f"[{name}] C7 control wrong-sided X'_u X_u^-1: crossing-edge fact FAILS on {c7}/{c5} triples")
        print(f"[{name}] item 5 identity on {i5} quadruples OK; wrong-sided version differs on {i5w}")
        G, worst, maxPhi = run(spec, seed, trials=12)
        print(f"[{name}] C1 Psi(mu)=Psi(mu^sym), C3 Phi invariance, C4 expansion identity: 12 trials OK")
        print(f"[{name}] C2 Condition&Round - Psi(mu^sym) >= 0, min slack = {float(worst['C2_slack']):.4f}")
        print(f"[{name}] C4 main term <= (Psi1+Psi2)/(2 beta^2), min slack = {float(worst['C4main_slack']):.4f}")
        print(f"[{name}] C4 lem:relating-ent-j bound holds, min slack = {float(worst['C4_slack']):.4f};"
              f" max Phi(D) = {float(maxPhi):.4f}")
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
