#!/usr/bin/env python3
"""Brute-force checks for two nodes of swarm-0917-w10-w10-ugc-break.

Part A: unique-games-lift-to-group-shift-games-on-the-same-host.
  A unique game U over [k] is disguised by a random per-vertex gauge. It is
  then tree-gauged and split into orbits of its holonomy group H. Each orbit
  game U_i is lifted to the left-shift game L_i over H_i = H|O_i on the same
  graph, and the script checks:
    (A1) val(L_i) <= val(U_i), and projecting an optimal lift labels U with
         value >= val(L_i);
    (A2) val(L_i) >= val(U_i) / |K_i|, where K_i = Stab(o_i);
    (A3) averaging over all fibre choices of an optimal orbit labeling
         gives exactly val(sigma') / |K_i|;
    (A4) max_i val(U_i) >= val(U) / t, and t |K_i| <= k!.

Part B: left-shift-games-carry-the-bafna-minzer-shift-symmetries.
  Over the non-abelian groups S_3 and Q_8, it checks on random left-shift
  games and on random honest distributions over labelings, exactly, with
  Fractions:
    (B1) right symmetrization preserves value and gives uniform marginals;
    (B2) Pr[X_v = s | X_u = e] = Pr[X_v X_u^-1 = s];
    (B3) E[val_v | X_v X_u^-1 = s] = E[val_v | X_u = e, X_v = s];
    (B4) crossing edges violate: if b = h a and b' = h a' then
         a^-1 a' = b^-1 b' (exhaustive);
    (B5) [a^-1 a' = b^-1 b'] == [b a^-1 = b' a'^-1] (exhaustive);
    (B6) Condition&Round with X_u = e has expected value >= Psi(mu_sym);
    (B7) random constraints: each fixed labeling satisfies a uniformly random
         left shift with probability exactly 1/|A|;
    (B8) control: the wrong-side difference a a'^-1 is NOT invariant along
         doubly satisfied edges in a non-abelian group.
"""
import itertools
import math
import random
from fractions import Fraction as Fr


# ---------------------------------------------------------------- helpers
def comp(p, q):
    """(p o q)(x) = p(q(x)) for permutations as tuples."""
    return tuple(p[q[i]] for i in range(len(q)))


def inv(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def closure(gens, k):
    ident = tuple(range(k))
    seen = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for a in frontier:
            for g in gens:
                b = comp(g, a)
                if b not in seen:
                    seen.add(b)
                    nxt.append(b)
        frontier = nxt
    return seen


def random_connected_graph(n, extra, rng):
    edges = []
    for v in range(1, n):
        edges.append((rng.randrange(v), v))
    pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
    rng.shuffle(pairs)
    have = set(edges)
    for (u, v) in pairs:
        if extra == 0:
            break
        if (u, v) not in have:
            edges.append((u, v))
            have.add((u, v))
            extra -= 1
    return edges


# ---------------------------------------------------------------- Part A
def ug_value(n, cons, lab):
    """cons: list of (u, v, pi, w) meaning lab[v] == pi[lab[u]]."""
    tot = sum(w for (_, _, _, w) in cons)
    sat = sum(w for (u, v, pi, w) in cons if lab[v] == pi[lab[u]])
    return Fr(sat, tot)


def tree_gauge(n, cons, k):
    """BFS tree gauge from vertex 0: every tree constraint becomes id."""
    ident = tuple(range(k))
    g = {0: ident}
    adj = {v: [] for v in range(n)}
    for idx, (u, v, pi, w) in enumerate(cons):
        adj[u].append(idx)
        adj[v].append(idx)
    order = [0]
    tree = set()
    while order:
        x = order.pop()
        for idx in adj[x]:
            u, v, pi, w = cons[idx]
            if u == x and v not in g:
                g[v] = comp(g[u], inv(pi))
                tree.add(idx)
                order.append(v)
            elif v == x and u not in g:
                g[u] = comp(g[v], pi)
                tree.add(idx)
                order.append(u)
    gauged = [(u, v, comp(comp(g[v], pi), inv(g[u])), w)
              for (u, v, pi, w) in cons]
    for idx in tree:
        assert gauged[idx][2] == ident
    return g, gauged


def orbits(H, k):
    left = set(range(k))
    out = []
    while left:
        o = min(left)
        orb = sorted({h[o] for h in H})
        out.append(orb)
        left -= set(orb)
    return out


def best(n, alphabet, satisfied, cons):
    tot = sum(c[-1] for c in cons)
    bestv, bestlab = Fr(-1), None
    for lab in itertools.product(alphabet, repeat=n):
        s = sum(c[-1] for c in cons if satisfied(lab, c))
        if s > bestv * tot:
            bestv, bestlab = Fr(s, tot), lab
    return bestv, bestlab


def part_A(rng, groups, trials):
    report = []
    for (name, k, gens, n, extra) in groups:
        H0 = sorted(closure(gens, k))
        for trial in range(trials):
            edges = random_connected_graph(n, extra, rng)
            hidden = [rng.randrange(k) for _ in range(n)]
            cons = []
            for (u, v) in edges:
                if rng.random() < 0.7:
                    cands = [h for h in H0 if h[hidden[u]] == hidden[v]]
                    cands = cands or H0   # hidden labels in different orbits
                else:
                    cands = H0
                cons.append((u, v, rng.choice(cands), rng.randint(1, 3)))
            # disguise by a random per-vertex gauge from S_k
            S_k = list(itertools.permutations(range(k)))
            dis = [rng.choice(S_k) for _ in range(n)]
            cons = [(u, v, comp(comp(dis[v], pi), inv(dis[u])), w)
                    for (u, v, pi, w) in cons]
            valU, _ = best(n, range(k),
                           lambda lab, c: lab[c[1]] == c[2][lab[c[0]]], cons)
            g, gauged = tree_gauge(n, cons, k)
            H = closure([c[2] for c in gauged], k)
            orbs = orbits(H, k)
            t = len(orbs)
            orbit_vals = []
            stab_sizes = []
            for O in orbs:
                o = O[0]
                pos = {x: i for i, x in enumerate(O)}

                def restrict(h):
                    return tuple(pos[h[x]] for x in O)
                Hi = sorted({restrict(h) for h in H})
                Ki = [a for a in Hi if a[0] == 0]
                # orbit game on labels 0..|O|-1 (positions in O)
                ocons = [(u, v, restrict(pi), w) for (u, v, pi, w) in gauged]
                valUi, labUi = best(
                    n, range(len(O)),
                    lambda lab, c: lab[c[1]] == c[2][lab[c[0]]], ocons)
                orbit_vals.append(valUi)
                # lifted left-shift game over Hi on the same graph
                valLi, labLi = best(
                    n, Hi,
                    lambda lab, c: lab[c[1]] == comp(c[2], lab[c[0]]), ocons)
                # (A1) projection
                proj = [a[0] for a in labLi]
                sigma = [g[v].index(O[proj[v]]) for v in range(n)]
                # sigma_v = g_v^-1(O[proj_v]); check value in the ORIGINAL U
                assert all(g[v][sigma[v]] == O[proj[v]] for v in range(n))
                vproj = ug_value(n, cons, sigma)
                assert valLi <= valUi, (name, trial)
                assert vproj >= valLi, (name, trial)
                # (A2)
                assert valLi * len(Ki) >= valUi, (name, trial, valLi, valUi)
                # (A3) exact average over all fibre choices of labUi
                fibres = [[a for a in Hi if a[0] == labUi[v]]
                          for v in range(n)]
                tot = sum(c[3] for c in ocons)
                acc = Fr(0)
                cnt = 0
                for h in itertools.product(*fibres):
                    s = sum(c[3] for c in ocons
                            if h[c[1]] == comp(c[2], h[c[0]]))
                    acc += Fr(s, tot)
                    cnt += 1
                assert acc / cnt == valUi / len(Ki), (name, trial)
                assert t * len(Ki) <= math.factorial(k)
                stab_sizes.append(len(Ki))
            # (A4)
            assert max(orbit_vals) <= valU <= sum(orbit_vals)
            assert max(orbit_vals) * t >= valU
            report.append((name, trial, "|H|=%d" % len(H), "t=%d" % t,
                           "|K_i|=%s" % stab_sizes, "val(U)=%s" % valU,
                           "val(U_i)=%s" % [str(x) for x in orbit_vals]))
    return report


# ---------------------------------------------------------------- Part B
class Group:
    def __init__(self, name, elems, mul):
        self.name = name
        self.E = list(elems)
        self.idx = {x: i for i, x in enumerate(self.E)}
        m = len(self.E)
        self.T = [[self.idx[mul(a, b)] for b in self.E] for a in self.E]
        self.e = next(i for i in range(m)
                      if all(self.T[i][j] == j for j in range(m)))
        self.I = [next(j for j in range(m) if self.T[i][j] == self.e)
                  for i in range(m)]
        self.n = m

    def mul(self, a, b):
        return self.T[a][b]


def make_S3():
    elems = list(itertools.permutations(range(3)))
    return Group("S3", elems, comp)


def make_Q8():
    # quaternion units; products of the basis units i, j, k with signs
    table = {('1', '1'): (1, '1'), ('1', 'i'): (1, 'i'), ('1', 'j'): (1, 'j'),
             ('1', 'k'): (1, 'k'), ('i', '1'): (1, 'i'), ('i', 'i'): (-1, '1'),
             ('i', 'j'): (1, 'k'), ('i', 'k'): (-1, 'j'), ('j', '1'): (1, 'j'),
             ('j', 'i'): (-1, 'k'), ('j', 'j'): (-1, '1'), ('j', 'k'): (1, 'i'),
             ('k', '1'): (1, 'k'), ('k', 'i'): (1, 'j'), ('k', 'j'): (-1, 'i'),
             ('k', 'k'): (-1, '1')}
    elems = [(s, u) for s in (1, -1) for u in '1ijk']

    def mul(a, b):
        s, u = table[(a[1], b[1])]
        return (a[0] * b[0] * s, u)
    return Group("Q8", elems, mul)


def part_B(rng, G, trials, n=4):
    A = range(G.n)
    e, mul, I = G.e, G.mul, G.I
    # (B4), (B5), (B7), (B8) exhaustive over the group
    for a, a2, h in itertools.product(A, A, A):
        b, b2 = mul(h, a), mul(h, a2)
        assert mul(I[a], a2) == mul(I[b], b2)          # B4
    for a, a2, b, b2 in itertools.product(A, A, A, A):
        lhs = mul(I[a], a2) == mul(I[b], b2)
        rhs = mul(b, I[a]) == mul(b2, I[a2])
        assert lhs == rhs                              # B5
    wrong_side_breaks = any(
        mul(a, I[a2]) != mul(mul(h, a), I[mul(h, a2)])
        for a, a2, h in itertools.product(A, A, A))
    assert wrong_side_breaks                           # B8
    for x, y in itertools.product(A, A):
        assert sum(1 for h in A if y == mul(h, x)) == 1  # B7
    for trial in range(trials):
        edges = random_connected_graph(n, 2, rng)
        cons = [(u, v, rng.randrange(G.n), rng.randint(1, 3))
                for (u, v) in edges]
        W = sum(c[3] for c in cons)
        deg = [0] * n
        nbrs = [[] for _ in range(n)]
        for (u, v, b, w) in cons:
            deg[u] += w
            deg[v] += w
            nbrs[u].append((v, I[b], w))   # read from u: X_u = b^-1 X_v
            nbrs[v].append((u, b, w))      # read from v: X_v = b X_u
        pi = [Fr(d, 2 * W) for d in deg]

        def val(X):
            return Fr(sum(w for (u, v, b, w) in cons if X[v] == mul(b, X[u])),
                      W)

        def valv(X, v):
            return Fr(sum(w for (x, b, w) in nbrs[v] if X[x] == mul(b, X[v])),
                      deg[v])
        # random honest distribution: noise plus one planted tree solution
        mu = {}
        for _ in range(6):
            X = tuple(rng.randrange(G.n) for _ in range(n))
            mu[X] = mu.get(X, 0) + rng.randint(1, 5)
        X = [None] * n
        X[0] = rng.randrange(G.n)
        changed = True
        while changed:
            changed = False
            for (u, v, b, w) in cons:
                if X[u] is not None and X[v] is None:
                    X[v] = mul(b, X[u])
                    changed = True
                elif X[v] is not None and X[u] is None:
                    X[u] = mul(I[b], X[v])
                    changed = True
        mu[tuple(X)] = mu.get(tuple(X), 0) + 10
        Z = sum(mu.values())
        mu = {k2: Fr(v2, Z) for k2, v2 in mu.items()}
        # (B1) right symmetrization X -> X t
        sym = {}
        for X, p in mu.items():
            for t in A:
                Y = tuple(mul(x, t) for x in X)
                sym[Y] = sym.get(Y, 0) + p / G.n
        assert sum(p * val(X) for X, p in mu.items()) == \
            sum(p * val(X) for X, p in sym.items())
        for u in range(n):
            for a in A:
                assert sum(p for X, p in sym.items() if X[u] == a) == \
                    Fr(1, G.n)

        def pr(pred):
            return sum(p for X, p in sym.items() if pred(X))

        def ex(f, pred):
            return sum(p * f(X) for X, p in sym.items() if pred(X))
        Psi = Fr(0)
        rounded = Fr(0)
        for u in range(n):
            pu = pr(lambda X: X[u] == e)
            cond = [{s: pr(lambda X: X[u] == e and X[v] == s) / pu
                     for s in A} for v in range(n)]
            for v in range(n):
                for s in A:
                    diff = pr(lambda X: mul(X[v], I[X[u]]) == s)
                    assert cond[v][s] == diff                     # B2
                    if diff:
                        lft = ex(lambda X: valv(X, v),
                                 lambda X: mul(X[v], I[X[u]]) == s) / diff
                        rgt = ex(lambda X: valv(X, v),
                                 lambda X: X[u] == e and X[v] == s) / \
                            pr(lambda X: X[u] == e and X[v] == s)
                        assert lft == rgt                          # B3
                        Psi += pi[u] * pi[v] * diff * diff * lft
            ru = Fr(0)
            for v in range(n):
                for (x, b, w) in nbrs[v]:
                    ru += pi[v] * Fr(w, deg[v]) * sum(
                        cond[v][s] * cond[x][mul(b, s)] for s in A)
            rounded += pi[u] * ru
        assert rounded >= Psi                                      # B6
    return True


def main():
    rng = random.Random(20260918)
    groups = [
        ("S3-on-3", 3, [(1, 0, 2), (1, 2, 0)], 6, 4),
        ("S4-on-4", 4, [(1, 0, 2, 3), (1, 2, 3, 0)], 4, 3),
        ("A4-on-4", 4, [(1, 2, 0, 3), (0, 2, 3, 1)], 4, 3),
        ("D4-on-4", 4, [(1, 2, 3, 0), (3, 2, 1, 0)], 5, 3),
        ("S3xZ2-on-3+2", 5, [(1, 0, 2, 3, 4), (1, 2, 0, 3, 4),
                             (0, 1, 2, 4, 3)], 4, 3),
    ]
    rep = part_A(rng, groups, trials=6)
    for r in rep:
        print("A", *r)
    nonreg = sum(1 for r in rep if "|K_i|=[1]" != r[4] and
                 any(x > 1 for x in eval(r[4].split("=")[1])))
    print("Part A: %d instances (%d with a non-regular orbit), "
          "checks A1-A4 passed" % (len(rep), nonreg))
    for G in (make_S3(), make_Q8()):
        part_B(rng, G, trials=4)
        print("Part B: %s, checks B1-B8 passed" % G.name)


if __name__ == "__main__":
    main()
