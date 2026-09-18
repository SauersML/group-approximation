# Free group F(a,b) utilities: words are lists of ints, a=1, b=2, inverses negative.
# Stallings folding for membership and conjugacy of finitely generated subgroups.


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def inv(w):
    return [-x for x in reversed(w)]


def mul(*ws):
    r = []
    for w in ws:
        r = red(r + list(w))
    return r


def apply(phi, w):
    """phi: dict {1: word, 2: word}, an endomorphism of F(a,b)."""
    r = []
    for x in w:
        r = red(r + (phi[x] if x > 0 else inv(phi[-x])))
    return r


def core(gens):
    """Folded Stallings graph of <gens>. Returns (G, base), G[u][label] = v."""
    edges = []
    n = 1
    for g in gens:
        g = red(g)
        if not g:
            continue
        u = 0
        for i, x in enumerate(g):
            v = 0 if i == len(g) - 1 else n
            if v:
                n += 1
            edges.append((u, x, v) if x > 0 else (v, -x, u))
            u = v
    par = list(range(n))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    while True:
        M = {}
        merged = False
        for (u, l, v) in edges:
            for key, w in (((f(u), l), f(v)), ((f(v), -l), f(u))):
                if key in M and f(M[key]) != f(w):
                    a, b = sorted((f(M[key]), f(w)))
                    par[b] = a
                    merged = True
                else:
                    M[key] = w
        if not merged:
            break
    G = {}
    for (u, l, v) in edges:
        G.setdefault(f(u), {})[l] = f(v)
        G.setdefault(f(v), {})[-l] = f(u)
    return G, f(0)


def member(gens, w, C=None):
    G, b = C if C else core(gens)
    u = b
    for x in red(w):
        if x not in G[u]:
            return False
        u = G[u][x]
    return u == b


def trim(G):
    G = {u: dict(d) for u, d in G.items()}
    ch = True
    while ch:
        ch = False
        for u in list(G):
            if u in G and len(G[u]) == 1:
                (l, v), = G[u].items()
                del G[u]
                del G[v][-l]
                ch = True
    return G


def canon(G):
    best = None
    for s in G:
        m = {s: 0}
        order = [s]
        i = 0
        code = []
        while i < len(order):
            u = order[i]
            i += 1
            for l in (1, -1, 2, -2):
                if l in G[u]:
                    v = G[u][l]
                    if v not in m:
                        m[v] = len(order)
                        order.append(v)
                    code.append((m[u], l, m[v]))
        c = tuple(code)
        if best is None or c < best:
            best = c
    return best


def conj_class(gens):
    G, b = core(gens)
    return canon(trim(G))
