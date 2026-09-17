#!/usr/bin/env python3
"""SAT test: does the ball B_R of Thompson's group F over S = A_k = {x0^±1,...,xk^±1}
carry a geodesic combing with synchronous fellow-traveller constant K?
A geodesic combing assigns to every g in B_R one geodesic path p_g (p_g(t) = g for t >= |g|),
with d_S(p_g(t), p_h(t)) <= K for all t whenever h = g s, s in S.
UNSAT at (R,K) proves: F admits no geodesic combing over S with constant K (restriction argument),
hence no geodesic (e.g. shortlex) automatic structure over S with fellow-traveller constant K.
Usage: geocomb_sat.py k R K [group]    group in {F, Z2, BS12} (calibration)"""
import sys, time
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from fastF import rmul, inv, ID, X0, X1
from pysat.solvers import Solver

def gensF(k):
    xs = [X0, X1]
    for n in range(2, k + 1):
        xs.append(rmul(rmul(X0, xs[n - 1]), inv(X0)))   # t -> X0^-1(x_{n-1}(X0 t)): support [1-2^-n,1]
    return xs

# calibration groups as tuples with explicit multiplication
def z2_gens():
    return [("vec", (1, 0)), ("vec", (0, 1))]

class Grp:
    def __init__(self, name, k=1):
        self.name = name
        if name == "F":
            xs = gensF(k)
            self.S = []
            for x in xs:
                self.S += [x, inv(x)]
            self.id = ID
            self.mul = rmul
            self.inv = inv
        elif name == "Z2":
            self.S = [(1, 0), (-1, 0), (0, 1), (0, -1)]
            self.id = (0, 0)
            self.mul = lambda a, b: (a[0] + b[0], a[1] + b[1])
            self.inv = lambda a: (-a[0], -a[1])
        elif name == "F2":
            def red(w):
                st = []
                for c in w:
                    if st and st[-1] == c.swapcase():
                        st.pop()
                    else:
                        st.append(c)
                return "".join(st)
            self.S = ["a", "A", "b", "B"]
            self.id = ""
            self.mul = lambda g, h: red(g + h)
            self.inv = lambda g: "".join(c.swapcase() for c in reversed(g))
        elif name == "Z3":
            self.S = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
            self.id = (0, 0, 0)
            self.mul = lambda a, b: tuple(x + y for x, y in zip(a, b))
            self.inv = lambda a: tuple(-x for x in a)
        elif name == "BS12":
            # elements (x, e): affine map t -> 2^e t + x, x dyadic; a: t->t+1 ; b: t->2t
            from fractions import Fraction as Q
            self.S = [(Q(1), 0), (Q(-1), 0), (Q(0), 1), (Q(0), -1)]
            self.id = (Q(0), 0)
            # g then s as maps applied: (g*s)(t) = g(s(t))  -> 2^eg (2^es t + xs) + xg
            self.mul = lambda g, s: (g[0] + (Q(2) ** g[1]) * s[0], g[1] + s[1])
            self.inv = lambda g: (-(Q(2) ** (-g[1])) * g[0], -g[1])

def build(G, R, K):
    dist = {G.id: 0}
    layers = [[G.id]]
    for L in range(1, R + 1):
        nxt = []
        for g in layers[-1]:
            for s in G.S:
                h = G.mul(g, s)
                if h not in dist:
                    dist[h] = L
                    nxt.append(h)
        layers.append(nxt)
    small = {g for g, d in dist.items() if d <= K}
    Sinv = [G.inv(s) for s in G.S]
    elems = [g for l in layers for g in l]
    # geodesic intervals
    I = {}
    for g in elems:
        n = dist[g]
        lay = [None] * (n + 1)
        lay[n] = [g]
        for t in range(n - 1, -1, -1):
            cur = set()
            for u in lay[t + 1]:
                for si in Sinv:
                    v = G.mul(u, si)
                    if dist.get(v) == t:
                        cur.add(v)
            lay[t] = sorted(cur, key=repr)
        I[g] = lay
    return dist, layers, elems, I, small

def solve(G, R, K, verbose=True, core=False):
    t0 = time.time()
    dist, layers, elems, I, small = build(G, R, K)
    var = {}
    def V(g, t, u):
        key = (g, t, u)
        if key not in var:
            var[key] = len(var) + 1
        return var[key]
    clauses = []
    def lay(g, t):
        L = I[g]
        return L[t] if t < len(L) else [g]
    for g in elems:
        n = dist[g]
        for t in range(n + 1):
            vs = [V(g, t, u) for u in I[g][t]]
            clauses.append(vs)
            for i in range(len(vs)):
                for j in range(i + 1, len(vs)):
                    clauses.append([-vs[i], -vs[j]])
            if t < n:
                nxt = set(I[g][t + 1])
                for u in I[g][t]:
                    succ = [V(g, t + 1, G.mul(u, s)) for s in G.S if G.mul(u, s) in nxt]
                    clauses.append([-V(g, t, u)] + succ)
    smallL = list(small)
    nbcache = {}
    def NB(u):
        r = nbcache.get(u)
        if r is None:
            r = set(G.mul(u, b) for b in smallL)
            nbcache[u] = r
        return r
    nft = 0
    edges = []
    edge_ranges = []
    for g in elems:
        for s in G.S:
            h = G.mul(g, s)
            if dist.get(h, R + 1) > R or dist[h] < dist[g]:
                continue
            if dist[h] == dist[g] and repr(h) < repr(g):
                continue
            T = max(dist[g], dist[h])
            edge_start = len(clauses)
            for t in range(1, T):
                A = lay(g, t); B = lay(h, t)
                Bset = set(B)
                for u in A:
                    near = [w for w in B if w in NB(u)]
                    lu = [V(g, t, u)] if t <= dist[g] else []
                    if t > dist[g]:
                        # p_g(t) = g fixed: require p_h(t) near g
                        clauses.append([V(h, t, w) for w in near] if near else [])
                        break
                    clauses.append([-V(g, t, u)] + [V(h, t, w) for w in near])
                    nft += 1
                if t <= dist[h]:
                    for w in B:
                        near = [u for u in A if u in NB(w)]
                        if t <= dist[g]:
                            clauses.append([-V(h, t, w)] + [V(g, t, u) for u in near])
            if core:
                sel = len(var) + 1 + len(edges)
                edges.append((g, s, h))
                edge_ranges.append((edge_start, len(clauses)))
    if core:
        base = len(var)
        guarded = [c for c in clauses]
        for i, (a, b) in enumerate(edge_ranges):
            for j in range(a, b):
                guarded[j] = clauses[j] + [-(base + 1 + i)]
        assumps = [base + 1 + i for i in range(len(edges))]
        with Solver(name="cadical153", bootstrap_with=guarded) as S:
            res = S.solve(assumptions=assumps)
            if not res:
                cr = sorted(set(S.get_core()))
                # shrink greedily
                cur = list(cr)
                changed = True
                while changed:
                    changed = False
                    for x in list(cur):
                        trial = [y for y in cur if y != x]
                        if not S.solve(assumptions=trial):
                            cur = sorted(set(S.get_core()))
                            changed = True
                            break
                print("core edges:", len(cur))
                for x in cur:
                    g, sgen, h = edges[x - base - 1]
                    print("  |g|=%d |h|=%d  g=%s  s=%s" % (dist[g], dist[h], word_of(G, dist, g), word_of(G, dist, sgen)))
    elif any(len(c) == 0 for c in clauses):
        res = False
    else:
        with Solver(name="cadical153", bootstrap_with=clauses) as S:
            res = S.solve()
    if verbose:
        print("group=%s R=%d K=%d |B_R|=%d vars=%d clauses=%d -> %s  (%.1fs)" % (
            G.name, R, K, len(elems), len(var), len(clauses), "SAT" if res else "UNSAT", time.time() - t0), flush=True)
    return res

def word_of(G, dist, g):
    names = ["a", "A", "b", "B", "c", "C", "d", "D"]
    w = []
    while dist[g] > 0:
        for i, s in enumerate(G.S):
            u = G.mul(g, G.inv(s))
            if dist.get(u, 99) == dist[g] - 1:
                w.append(names[i] if i < len(names) else "g%d" % i)
                g = u
                break
    return "".join(reversed(w)) or "1"

if __name__ == "__main__":
    k = int(sys.argv[1]); R = int(sys.argv[2]); K = int(sys.argv[3])
    grp = sys.argv[4] if len(sys.argv) > 4 else "F"
    solve(Grp(grp, k), R, K, core=("core" in sys.argv))
