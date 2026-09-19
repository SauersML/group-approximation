#!/usr/bin/env python3
"""Checks for correlated-products-cannot-substitute-rounds-for-alphabet.

Exact (Fraction) checks of the tensor step of the proof route on small
mu-products of bipartite unique games, with random couplings mu:

  T1  tensor feasibility on the product probability space Omega^l:
      nonnegativity, sum of squared norms = 1, disjoint supports per vertex;
  T2  the objective of H at every constraint, computed directly on Omega^l,
      equals the product of the base objectives;
  T3  sdp+-objective(H) >= 1 - sum_j D_j (1 - objective(G_j)), with D_j the
      max density of the j-th marginal of mu;
  T4  union-bound completeness opt(H) >= 1 - sum_j D_j (1 - opt(G_j)), by
      brute force;
  T5  illustration of (H2) on these instances: opt(H) >= 1 - 2 sqrt(2 (1 - obj_H));
  T6  the diagonal coupling: eta_out = 1 - opt(H) is strictly below the
      union-bound sum, so union-bound completeness is a real hypothesis;
  T7  elementary inequalities: 1 - prod a_j <= sum (1 - a_j) on [0,1],
      and 1.5 * C_+^2 = 12 C_3 for C_+ = 2 sqrt(2 C_3).

T5 is an illustration only; (H2) is imported, not checked.
Writes output.txt next to this file and ends in ALL PASS.
"""
import itertools
import math
import os
import random
from fractions import Fraction as F

random.seed(20260919)
OUT = []
FAIL = []


def log(s):
    OUT.append(s)
    print(s)


def check(name, cond):
    log(("PASS " if cond else "FAIL ") + name)
    if not cond:
        FAIL.append(name)


# ---------------------------------------------------------------- games
def random_game(nL, nR, k, m, planted=True):
    """Bipartite UG: list of (u, v, perm, weight). Planted labelling satisfied
    on most edges so that objectives are near 1 and T3 is not vacuous."""
    sig_L = [random.randrange(k) for _ in range(nL)]
    sig_R = [random.randrange(k) for _ in range(nR)]
    edges = []
    for e in range(m):
        u, v = random.randrange(nL), random.randrange(nR)
        perm = list(range(k))
        random.shuffle(perm)
        if planted and e != 0:
            # force perm(sig_L[u]) = sig_R[v]
            j = perm.index(sig_R[v])
            perm[j], perm[sig_L[u]] = perm[sig_L[u]], perm[j]
        edges.append((u, v, tuple(perm), F(1)))
    tot = sum(w for *_, w in edges)
    edges = [(u, v, p, w / tot) for (u, v, p, w) in edges]
    return dict(nL=nL, nR=nR, k=k, edges=edges, sigL=sig_L, sigR=sig_R)


def rational_unit(d):
    """Nonnegative rational unit vector of length d (inverse stereographic)."""
    if d == 1:
        return [F(1)]
    t = [random.randint(-3, 3) for _ in range(d - 1)]
    s = sum(x * x for x in t)
    x = [F(2 * ti, s + 1) for ti in t] + [F(s - 1, s + 1)]
    return [abs(y) for y in x]


def random_solution(game, M, sq):
    """Feasible sdp+ solution on Omega = [M] with uniform measure.
    Each vertex partitions Omega among labels (biased to the planted label).
    About 3/4 of the vertices use indicators; the rest use sqrt(M) * rational unit
    vectors restricted to the parts (needs sq = sqrt(M) rational)."""
    k = game["k"]
    sol = {}
    for side, n, sig in (("L", game["nL"], game["sigL"]), ("R", game["nR"], game["sigR"])):
        for u in range(n):
            lab = [sig[u] if random.random() < 0.93 else random.randrange(k) for _ in range(M)]
            if random.random() < 0.75:
                vals = [F(1)] * M
            else:
                x = rational_unit(M)
                vals = [sq * xi for xi in x]
            f = {i: [vals[w] if lab[w] == i else F(0) for w in range(M)] for i in range(k)}
            sol[(side, u)] = f
    return sol


def inner(f, g, mu):
    return sum(a * b * m for a, b, m in zip(f, g, mu))


def edge_val(game, sol, mu, e):
    u, v, p, _ = e
    return sum(inner(sol[("L", u)][i], sol[("R", v)][p[i]], mu) for i in range(game["k"]))


def objective(game, sol, mu):
    return sum(e[3] * edge_val(game, sol, mu, e) for e in game["edges"])


def feasible(game, sol, mu):
    ok = True
    for key, f in sol.items():
        k = game["k"]
        ok &= all(x >= 0 for i in range(k) for x in f[i])
        ok &= sum(inner(f[i], f[i], mu) for i in range(k)) == 1
        for i in range(k):
            for j in range(i + 1, k):
                ok &= all(not (a != 0 and b != 0) for a, b in zip(f[i], f[j]))
    return ok


# ----------------------------------------------------------- mu-products
def random_coupling(games, diag=False):
    """Random probability distribution on E_1 x ... x E_l (sparse support)."""
    Es = [range(len(g["edges"])) for g in games]
    if diag:
        m = len(games[0]["edges"])
        return {tuple([a] * len(games)): games[0]["edges"][a][3] for a in range(m)}
    supp = list(itertools.product(*Es))
    random.shuffle(supp)
    supp = supp[: max(3, (3 * len(supp)) // 4)]
    w = [F(random.randint(4, 6)) for _ in supp]
    tot = sum(w)
    return {s: x / tot for s, x in zip(supp, w)}


def densities(games, mu):
    D = []
    for j, g in enumerate(games):
        marg = [F(0)] * len(g["edges"])
        for s, p in mu.items():
            marg[s[j]] += p
        D.append(max((marg[a] / g["edges"][a][3]) for a in range(len(g["edges"]))))
    return D


def product_game(games, mu):
    l = len(games)
    edges = []
    for s, p in mu.items():
        es = [games[j]["edges"][s[j]] for j in range(l)]
        edges.append((tuple(e[0] for e in es), tuple(e[1] for e in es), tuple(e[2] for e in es), p))
    return edges


def tensor_solution(games, sols, M):
    """f_{(u_j),(i_j)}(w_1..w_l) = prod_j f^{(j)}_{u_j,i_j}(w_j) on [M]^l."""
    l = len(games)
    atoms = list(itertools.product(range(M), repeat=l))
    tens = {}
    for side, nkey in (("L", "nL"), ("R", "nR")):
        for us in itertools.product(*[range(g[nkey]) for g in games]):
            for labs in itertools.product(*[range(g["k"]) for g in games]):
                vec = []
                for w in atoms:
                    x = F(1)
                    for j in range(l):
                        x *= sols[j][(side, us[j])][labs[j]][w[j]]
                    vec.append(x)
                tens[(side, us, labs)] = vec
    return atoms, tens


def check_tensor(games, sols, mu_prod, M, tag):
    l = len(games)
    atoms, tens = tensor_solution(games, sols, M)
    muW = [F(1, M ** l)] * len(atoms)
    labsets = list(itertools.product(*[range(g["k"]) for g in games]))
    ok = True
    for side, nkey in (("L", "nL"), ("R", "nR")):
        for us in itertools.product(*[range(g[nkey]) for g in games]):
            vecs = [tens[(side, us, labs)] for labs in labsets]
            ok &= all(x >= 0 for v in vecs for x in v)
            ok &= sum(inner(v, v, muW) for v in vecs) == 1
            for a in range(len(vecs)):
                for b in range(a + 1, len(vecs)):
                    ok &= all(not (x != 0 and y != 0) for x, y in zip(vecs[a], vecs[b]))
    check(f"T1 [{tag}] tensor solution feasible on Omega^{l} ({len(atoms)} atoms)", ok)
    muB = [F(1, M)] * M
    ok2 = True
    objH = F(0)
    for s, p in mu_prod.items():
        us = tuple(games[j]["edges"][s[j]][0] for j in range(l))
        vs = tuple(games[j]["edges"][s[j]][1] for j in range(l))
        ps = [games[j]["edges"][s[j]][2] for j in range(l)]
        direct = F(0)
        for labs in labsets:
            img = tuple(ps[j][labs[j]] for j in range(l))
            direct += inner(tens[("L", us, labs)], tens[("R", vs, img)], muW)
        prod = F(1)
        for j in range(l):
            vj = edge_val(games[j], sols[j], muB, games[j]["edges"][s[j]])
            ok2 &= 0 <= vj <= 1
            prod *= vj
        ok2 &= direct == prod
        objH += p * direct
    check(f"T2 [{tag}] per-constraint objective on Omega^{l} = product of base objectives, all in [0,1]", ok2)
    return objH


def brute_opt(nL, nR, k, edges):
    """Exact opt of a bipartite UG given as (u, v, perm, w) with hashable u, v."""
    Ls = sorted({e[0] for e in edges})
    Rs = sorted({e[1] for e in edges})
    best = F(0)
    for lab in itertools.product(range(k), repeat=len(Ls)):
        L = dict(zip(Ls, lab))
        gain = {}
        for u, v, p, w in edges:
            key = (v, p[L[u]])
            gain[key] = gain.get(key, F(0)) + w
        tot = F(0)
        for v in Rs:
            tot += max((gain.get((v, b), F(0)) for b in range(k)), default=F(0))
        best = max(best, tot)
    return best


def perm_prod(ps, ks):
    """Encode the product permutation on prod [k_j] as a tuple on [K]."""
    labsets = list(itertools.product(*[range(k) for k in ks]))
    idx = {t: n for n, t in enumerate(labsets)}
    return tuple(idx[tuple(ps[j][t[j]] for j in range(len(ks)))] for t in labsets)


def as_ug(games, edgesH):
    ks = [g["k"] for g in games]
    K = math.prod(ks)
    return K, [(u, v, perm_prod(p, ks), w) for (u, v, p, w) in edgesH]


# ---------------------------------------------------------------- runs
def run_case(tag, specs, M, sq, brute):
    games = [random_game(*sp) for sp in specs]
    muB = [F(1, M)] * M
    sols = [random_solution(g, M, sq) for g in games]
    okf = all(feasible(g, s, muB) for g, s in zip(games, sols))
    check(f"T0 [{tag}] base solutions feasible for (2.7)-(2.8)", okf)
    objs = [objective(g, s, muB) for g, s in zip(games, sols)]
    mu = random_coupling(games)
    D = densities(games, mu)
    objH = check_tensor(games, sols, mu, M, tag)
    rhs = 1 - sum(Dj * (1 - oj) for Dj, oj in zip(D, objs))
    log(f"     base objectives {[float(o) for o in objs]}, densities {[float(d) for d in D]}")
    log(f"     obj_H = {float(objH):.6f} >= 1 - sum D_j(1-obj_j) = {float(rhs):.6f}")
    check(f"T3 [{tag}] coupling-blind tensor bound", objH >= rhs)
    check(f"T3 [{tag}] bound is non-vacuous (rhs > 0)", rhs > 0)
    if brute:
        opts = [brute_opt(g["nL"], g["nR"], g["k"], g["edges"]) for g in games]
        K, ug = as_ug(games, product_game(games, mu))
        optH = brute_opt(None, None, K, ug)
        ub = 1 - sum(Dj * (1 - oj) for Dj, oj in zip(D, opts))
        log(f"     opt(G_j) = {[float(o) for o in opts]}, opt(H) = {float(optH):.6f}")
        check(f"T4 [{tag}] opt(H) >= 1 - sum D_j (1 - opt_j) = {float(ub):.6f}", optH >= ub)
        t8 = 1 - 2 * math.sqrt(2 * float(1 - objH))
        check(f"T5 [{tag}] (illustration) opt(H) >= 1 - 2 sqrt(2(1-obj_H)) = {t8:.6f}", float(optH) >= t8 - 1e-12)


def run_diagonal():
    # base: 3 left, 3 right vertices, k = 2, a frustrated game
    g = random_game(3, 3, 2, 6, planted=False)
    opt = brute_opt(3, 3, 2, g["edges"])
    tries = 0
    while opt == 1 and tries < 50:
        g = random_game(3, 3, 2, 6, planted=False)
        opt = brute_opt(3, 3, 2, g["edges"])
        tries += 1
    games = [g, g]
    mu = random_coupling(games, diag=True)
    D = densities(games, mu)
    K, ug = as_ug(games, product_game(games, mu))
    optH = brute_opt(None, None, K, ug)
    eta_sigma = 2 * (1 - opt)
    log(f"     diagonal: opt(G) = {opt}, opt(H) = {optH}, D = {[str(d) for d in D]}, eta_Sigma = {eta_sigma}")
    check("T6 diagonal coupling has D = 1 in both coordinates", all(d == 1 for d in D))
    check("T6 diagonal coupling: eta_out = 1 - opt(H) < D * eta_Sigma", 1 - optH < eta_sigma)


def run_elementary():
    ok = True
    for _ in range(2000):
        l = random.randint(1, 6)
        a = [F(random.randint(0, 20), 20) for _ in range(l)]
        ok &= 1 - math.prod(a) <= sum(1 - x for x in a)
    check("T7 1 - prod a_j <= sum (1 - a_j) on 2000 random rational tuples in [0,1]", ok)
    ok2 = all(abs(1.5 * (2 * math.sqrt(2 * c)) ** 2 - 12 * c) < 1e-9 for c in (1, 2.5, 7, 100))
    check("T7 1.5 C_+^2 = 12 C_3 for C_+ = 2 sqrt(2 C_3)", ok2)


if __name__ == "__main__":
    log("== heterogeneous l = 2, alphabets (2, 3), M = 16 ==")
    run_case("l2-het", [(2, 2, 2, 4), (2, 2, 3, 4)], 16, F(4), brute=True)
    log("== homogeneous alphabet l = 2, k = 2, M = 4 ==")
    run_case("l2-hom", [(3, 3, 2, 5), (3, 3, 2, 5)], 4, F(2), brute=True)
    log("== heterogeneous l = 3, alphabets (2, 2, 3), M = 4 ==")
    run_case("l3-het", [(2, 2, 2, 3), (2, 2, 2, 3), (2, 2, 3, 3)], 4, F(2), brute=False)
    log("== diagonal coupling ==")
    run_diagonal()
    log("== elementary ==")
    run_elementary()
    log("ALL PASS" if not FAIL else f"FAILURES: {FAIL}")
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "output.txt"), "w") as fh:
        fh.write("\n".join(OUT) + "\n")
