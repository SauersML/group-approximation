# Irreducibility certificate for BMW data whose letter automaton has the shape <E, tau>: all letters except tau
# pairwise commute in H_x = pr_V(<A>) (checked exactly), so H_x is a quotient of Q = E * <tau>, E = (Z/2)^3 / R.
# Q has normal forms (alternating nonzero E-cosets and tau), hence decidable conjugacy (cyclic normal forms).
# Orbit-signalizer graph: for a word g and a vertex u whose g-orbit has length k, the section s = g^k|_u
# satisfies pr_V(s) = pr_V(u^-1 g^k u), so ord(s) = ord(g)/k whenever ord(g) is finite (k divides ord(g)).
# Edges g -> [s] (conjugacy class in Q, which maps onto conjugacy in H_x) with weight k.  A cycle of total
# weight > 1 forces ord(g) = ord(g)/(prod k); more generally the difference constraints below (with power
# relations c = r^j between nodes) are infeasible, so some node has infinite order in H_x.  Then H_x is infinite,
# pr_V(Gamma) is non-discrete and Gamma is irreducible (Burger-Mozes, Lattices in product of trees, Prop. 1.2).
# usage: irred_q.py census.json idx side Lu Lmax
import sys, json, itertools
from lo_census import load
from irred_tw import maps
from kernel import trivial
from irred_kps import act_word

def setup(G, side):
    L, n, invT, step = maps(G, side)
    invL = G.iA if side == 'V' else G.iB
    assert all(invL[a] == a for a in range(L)), 'all letters must be involutions'
    # tau: the letter whose sections are all itself
    taus = [a for a in range(L) if all(step(a, x)[1] == a for x in range(n))]
    assert taus, 'no letter with constant section'
    tau = taus[0]; Es = [a for a in range(L) if a != tau]
    for a, b in itertools.combinations(Es, 2):
        assert trivial(step, n, invT, (a, b, a, b)), f'letters {a},{b} do not commute in H_x'
    # R = masks of E-letters acting trivially
    R = []
    for m in range(1, 1 << len(Es)):
        w = tuple(Es[i] for i in range(len(Es)) if m >> i & 1)
        if trivial(step, n, invT, w): R.append(m)
    return L, n, invT, step, tau, Es, R

def make_ops(tau, Es, R):
    span = {0}
    for r in R: span |= {s ^ r for s in span}
    canon = lambda m: min(m ^ s for s in span)
    def push(out, x):
        if x == 'T':
            if out and out[-1] == 'T': out.pop()
            else: out.append('T')
        elif out and out[-1] != 'T':
            m = canon(out.pop() ^ x)
            if m: out.append(m)
        else:
            m = canon(x)
            if m: out.append(m)
    def nf(word):
        out = []
        for x in word: push(out, 'T' if x == tau else 1 << Es.index(x))
        return out
    def cyc(t):
        t = list(t)
        while len(t) >= 2:
            if t[0] != 'T' and t[-1] != 'T':
                out = []
                for x in t[1:-1] + [t[0] ^ t[-1]]: push(out, x)
                t = out
            elif t[0] == 'T' and t[-1] == 'T':
                t = t[1:-1]
            else:
                break
        if not t: return ()
        rots = [tuple(t[i:] + t[:i]) for i in range(len(t))]
        return min(rots, key=lambda r: tuple((0, x) if x != 'T' else (1, 0) for x in r))
    def tokens_to_word(t):
        w = []
        for x in t:
            if x == 'T': w.append(tau)
            else: w += [Es[i] for i in range(len(Es)) if x >> i & 1]
        return tuple(w)
    return nf, cyc, tokens_to_word

def search(G, side, Lu, Lmax):
    L, n, invT, step, tau, Es, R = setup(G, side)
    nf, cyc, t2w = make_ops(tau, Es, R)
    from irred_kps import reduced_words
    starts = [cyc(nf(w)) for w in [(tau,) + (e,) for e in Es] + [(tau, a, b) for a, b in itertools.combinations(Es, 2)]]
    starts = [s for s in starts if s]
    edges = {}; todo = list(dict.fromkeys(starts)); seen = set(todo)
    while todo:
        g = todo.pop(0); gw = t2w(g); out = []
        for u in reduced_words(n, invT, Lu):
            v, _ = act_word(step, gw, u); k = 1
            while v != u and k < 500: v, _ = act_word(step, gw, v); k += 1
            if v != u: continue
            _, s = act_word(step, gw * k, u)
            c = cyc(nf(s))
            if not c or len(c) > Lmax: continue
            out.append((c, k, u))
            if c not in seen: seen.add(c); todo.append(c)
        edges[g] = out
        if len(seen) > 5000: break
    # Difference constraints on x_c = log ord(c), assuming every node has finite order:
    #   section edge g -> s of weight k:  x_s = x_g - log k;
    #   c = r^j (as cyclic words):         x_r - log j <= x_c <= x_r.
    # A negative cycle (checked exactly on integers) makes the system infeasible, so some node has infinite order.
    def root(c):
        L = len(c)
        for p in range(1, L + 1):
            if L % p == 0 and c == c[:p] * (L // p): return c[:p], L // p
    cons = []                                   # (a, b, num, den): x_b <= x_a + log(num/den)
    for g, out in edges.items():
        for (c, k, u) in out:
            cons.append((g, c, 1, k, ('sec', u, k))); cons.append((c, g, k, 1, ('sec-', u, k)))
    for c in list(seen):
        r, j = root(c)
        if j > 1:
            r = cyc(nf(t2w(r)))
            cons.append((r, c, 1, 1, ('pow', j))); cons.append((c, r, j, 1, ('pow-', j)))
    import math
    V = sorted({x for cc in cons for x in cc[:2]}, key=str); ix = {v: i for i, v in enumerate(V)}
    dist = [0.0] * len(V); pred = [None] * len(V); last = None
    for it in range(len(V) + 1):
        last = None
        for (a_, b_, num, den, lab) in cons:
            w = math.log(num) - math.log(den)
            if dist[ix[a_]] + w < dist[ix[b_]] - 1e-9:
                dist[ix[b_]] = dist[ix[a_]] + w; pred[ix[b_]] = (a_, num, den, lab); last = b_
        if last is None: break
    if last is None:
        return dict(tau=tau, E=Es, R=R, nodes=len(seen), cycle=None)
    x = last
    for _ in range(len(V)): x = pred[ix[x]][0]
    cyc_nodes = []; y = x
    while True:
        a_, num, den, lab = pred[ix[y]]; cyc_nodes.append((a_, y, num, den, lab)); y = a_
        if y == x: break
    from fractions import Fraction
    prod = Fraction(1)
    for (_, _, num, den, _) in cyc_nodes: prod *= Fraction(num, den)
    assert prod < 1
    return dict(tau=tau, E=Es, R=R, nodes=len(seen), cycle_ratio=str(prod),
                cycle=[dict(frm=t2w(a_), to=t2w(b_), bound=f"{num}/{den}", why=lab) for (a_, b_, num, den, lab) in reversed(cyc_nodes)])

if __name__ == "__main__":
    path, idx, side, Lu, Lmax = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
    G = next(G for i, G in load(path) if i == idx)
    print(json.dumps(dict(census=path, idx=idx, side=side, Lu=Lu, Lmax=Lmax, **search(G, side, Lu, Lmax))), flush=True)
