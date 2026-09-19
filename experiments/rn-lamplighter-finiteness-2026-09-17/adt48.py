"""Check Almeida-Dantas-Oliveira-Tosti (arXiv:2609.01868) Example 4.8.
G = C_2 wr Z = F_2[t,1/t] x| t^Z.  Elements (p, k): p = frozenset of exponents (Laurent poly over F_2).
H = M x| <t^2>, M = (1+t^2)F_2[t^{+-1}], index 8.  f(m, 2j) = (phi(m), j) with
phi((1+s)A(s) + t(1+s)B(s)) = (1+t)A(t) + c*B(t), s = t^2; phi(1+t^2) = 1+t is the paper's datum,
c = phi(t+t^3) is NOT fixed by the paper (x[b,x^2]x^-1 lies in H but not in <[b,x^2],x^2>).
We compute the states reachable from the generators b=(1,0), x=(0,1) under the induced self-similar
action on the 8-ary tree, for every c of small support, and report whether the automaton is finite.
Usage: python3 adt48.py [maxstates]"""
import sys, itertools
def add(p, q): return frozenset(p ^ q)
def shift(p, k): return frozenset(e + k for e in p)
def mul(g, h): return (add(g[0], shift(h[0], g[1])), g[1] + h[1])
def inv(g): return (shift(g[0], -g[1]), -g[1])
def polydiv_1ps(p):
    # divide Laurent poly p (in F_2[s^{+-1}]) by (1+s); return quotient or None
    if not p: return frozenset()
    lo = min(p); q = set(); r = set(e - lo for e in p)
    hi = max(r); cur = set(r); out = set()
    for e in range(hi):
        if e in cur:
            out.add(e); cur ^= {e, e + 1}
    if cur: return None
    return frozenset(e + lo for e in out)
def reduce_mod(P):
    # residue of P mod (1+t)^2 in basis {0,1,t,1+t}: P(1) and P'(1)
    v0 = len(P) % 2
    v1 = sum(1 for e in P if e % 2) % 2   # derivative at 1 in char 2: sum of odd-exponent coeffs
    # a = a0 + a1 t : value a0+a1, derivative a1
    a1 = v1; a0 = (v0 + a1) % 2
    return frozenset(e for e, bit in ((0, a0), (1, a1)) if bit)
def phi(m, c):
    ev = frozenset(e // 2 for e in m if e % 2 == 0)
    od = frozenset((e - 1) // 2 for e in m if e % 2)
    A = polydiv_1ps(ev); B = polydiv_1ps(od)
    assert A is not None and B is not None, m
    res = frozenset()
    res = add(res, add(A, shift(A, 1)))           # (1+t)A(t)
    for e in B: res = add(res, shift(c, e))       # c*B(t)
    return res
REPS = [(a, e) for e in (0, 1) for a in (frozenset(), frozenset({0}), frozenset({1}), frozenset({0, 1}))]
def sections(g, c):
    out = []
    for r in REPS:
        gr = mul(g, r)
        a2 = reduce_mod(gr[0]); e2 = gr[1] % 2
        h = mul(inv((a2, e2)), gr)
        assert h[1] % 2 == 0
        out.append((phi(h[0], c), h[1] // 2))
    return out
def reach(c, cap):
    gens = [(frozenset({0}), 0), (frozenset(), 1), (frozenset(), -1)]
    seen = set(gens); todo = list(gens)
    while todo and len(seen) < cap:
        g = todo.pop()
        for s in sections(g, c):
            if s not in seen: seen.add(s); todo.append(s)
    return len(seen), max(len(g[0]) for g in seen), max(abs(g[1]) for g in seen)
if __name__ == "__main__":
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    for sup in itertools.chain.from_iterable(itertools.combinations(range(-2, 3), r) for r in range(0, 4)):
        c = frozenset(sup)
        n, ml, mk = reach(c, cap)
        print("c=%-18s states=%s%s maxlamps=%d max|k|=%d" % (sorted(c), n, "+" if n >= cap else "", ml, mk))

# ---- contraction and faithfulness tests ----
def closure(start, c, cap):
    seen = set(start); todo = list(start); edges = {}
    while todo:
        if len(seen) > cap: return None, None
        g = todo.pop(); ss = sections(g, c); edges[g] = ss
        for s in ss:
            if s not in seen: seen.add(s); todo.append(s)
    return seen, edges
def cyclic_core(seen, edges):
    # vertices lying on a directed cycle: iterate removing vertices with no path back
    import sys
    sys.setrecursionlimit(100000)
    idx = {}; low = {}; st = []; on = set(); comps = []; cnt = [0]
    def sc(v):
        idx[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on.add(v)
        for w in edges[v]:
            if w not in idx: sc(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v: break
            comps.append(comp)
    for v in seen:
        if v not in idx: sc(v)
    core = set()
    for comp in comps:
        if len(comp) > 1 or comp[0] in edges[comp[0]]: core.update(comp)
    return core
def nucleus(c, cap=20000, rounds=12):
    gens = [(frozenset({0}), 0), (frozenset(), 1), (frozenset(), -1)]
    seen, edges = closure(gens, c, cap)
    N = cyclic_core(seen, edges)
    for _ in range(rounds):
        prods = set(mul(a, b) for a in N for b in N) | N
        seen, edges = closure(prods, c, cap)
        if seen is None: return None
        N2 = cyclic_core(seen, edges)
        if N2 <= N: return N
        N = N | N2
    return None
def acts_trivially(g, c, cap=5000):
    seen, edges = closure([g], c, cap)
    if seen is None: return None
    for h in seen:
        for r, s in zip(REPS, [mul(h, r) for r in REPS]):
            if reduce_mod(s[0]) != r[0] or s[1] % 2 != r[1]: return False
    return True
def kernel_witness(c, rad=3):
    # search nonidentity elements with lamps in [-rad,rad], shift in [-1,1], acting trivially
    for k in (0, 1, -1):
        for r in range(1, 2 * rad + 2):
            for sup in itertools.combinations(range(-rad, rad + 1), r):
                g = (frozenset(sup), k)
                if acts_trivially(g, c): return g
    return None
