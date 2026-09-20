"""Exact relative-inertia census over random malnormal rank-2 hosts.

(RI_B): rk(J cap B : X) <= rk(J : X) for f.g. X <= B, J >= X.

Here X is of FINITE INDEX in B (the top-case regime of the w19 non-malnormal
counterexample), or of finite index in a sub-host C <= B (the (G_j) regime,
e.g. B = L_1, C = L_2).

k = 1 (exact, all g at once).  By the one-pair lemma (w20-fp-last1), every
J = <X, g> is an arc extension (harmless) or fold(Gamma_X / u~w).  For each
such J we compute Y = J cap B and decide rk(Y : X) <= 1 exactly:
  Y = X, or Gamma_X embeds in Gamma_Y with rk Y = rk X + 1, or Gamma_Y is a
  one-pair fold of Gamma_X.  Only pairs u', w' with the same image under the
  immersion Gamma_X -> Gamma_Y can fold into Gamma_Y (pruning, exact).

k = 2 (sampled, exact on the J side).  J = fold(Gamma_X / u1~w1, u2~w2).
Certificate rk(Y : X) <= 2 is searched through an intermediate Z = X, Z a
one-pair fold of Gamma_X inside Y, or Z = X * <h> an arc extension with the
arc an immersed path of Gamma_Y of bounded length.  Unresolved cases are
printed as CANDIDATE (not violations).

usage:
  census.py k1 seed trials host   (host = rand | L1 | L2 | L1overL2 | nonmal)
  census.py k2 seed trials host samples
  census.py selftest
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'fpbs-overfold-one-pair-2026-09-17'))
from folding import (fold, graph_of, rank, canon, rand_word, reduce_word,
                     phi, INV)  # noqa: E402
from ri_k1 import pullback, compact, embeds  # noqa: E402


# ---------------------------------------------------------------- graphs

def product_components(n1, E1, n2, E2):
    """All components of the product graph: list of (vertex set, edge count)."""
    edges = []
    idx = {}
    for x in range(n1):
        for y in range(n2):
            idx[(x, y)] = len(idx)
    parent = list(range(len(idx)))

    def find(z):
        while parent[z] != z:
            parent[z] = parent[parent[z]]
            z = parent[z]
        return z
    E2by = {}
    for (u, l, v) in E2:
        E2by.setdefault(l, []).append((u, v))
    for (u, l, v) in E1:
        for (u2, v2) in E2by.get(l, []):
            p, q = idx[(u, u2)], idx[(v, v2)]
            edges.append((p, q))
            rp, rq = find(p), find(q)
            if rp != rq:
                parent[rp] = rq
    comp_v, comp_e = {}, {}
    for z in range(len(idx)):
        comp_v.setdefault(find(z), set()).add(z)
    for (p, q) in edges:
        r = find(p)
        comp_e[r] = comp_e.get(r, 0) + 1
    diag = find(idx[(0, 0)])
    return [(r == diag, len(vs), comp_e.get(r, 0)) for r, vs in comp_v.items()]


def is_malnormal(n, E):
    """Core graph: malnormal iff every off-diagonal component of the self
    product is a forest (edges < vertices)."""
    for (isdiag, nv, ne) in product_components(n, E, n, E):
        if not isdiag and ne >= nv:
            return False
    return True


def image_map(nx, Ex, ny, Ey):
    """Vertex map of the based immersion Gamma_X -> Gamma_Y (X <= Y)."""
    outy = {(u, l): v for (u, l, v) in Ey}
    iny = {(v, l): u for (u, l, v) in Ey}
    adj = {}
    for (u, l, v) in Ex:
        adj.setdefault(u, []).append((l, v, 1))
        adj.setdefault(v, []).append((l, u, -1))
    m = {0: 0}
    q = [0]
    while q:
        v = q.pop()
        for (l, t, d) in adj.get(v, []):
            img = outy.get((m[v], l)) if d == 1 else iny.get((m[v], l))
            if img is None:
                return None
            if t not in m:
                m[t] = img
                q.append(t)
    return m


def subst_graph(n, sedges, words):
    """Schreier-type graph over abstract generators 0..r-1 (edges (p, i, q)),
    each i-edge replaced by a path spelling words[i] over {a,b}; folded core."""
    N = n
    edges = []
    for (p, i, q) in sedges:
        w = reduce_word(words[i])
        cur = p
        for t, c in enumerate(w):
            if t == len(w) - 1:
                nxt = q
            else:
                nxt = N
                N += 1
            if c in 'ab':
                edges.append((cur, c, nxt))
            else:
                edges.append((nxt, c.lower(), cur))
            cur = nxt
    m, E, root = fold(N, edges)
    # rebase at root[0]
    b = root[0]
    perm = {b: 0}
    for v in range(m):
        if v not in perm:
            perm[v] = len(perm)
    E = [(perm[u], l, perm[v]) for (u, l, v) in E]
    return compact(m, E)


def rand_transitive_action(r, n, rng):
    """r random permutations of {0..n-1} generating a transitive group."""
    while True:
        perms = []
        for _ in range(r):
            p = list(range(n))
            rng.shuffle(p)
            perms.append(p)
        seen = {0}
        q = [0]
        while q:
            x = q.pop()
            for p in perms:
                for y in (p[x], p.index(x)):
                    if y not in seen:
                        seen.add(y)
                        q.append(y)
        if len(seen) == n:
            return perms


def regular_action(perms):
    """Right regular action of the group generated by perms (tuples)."""
    n0 = len(perms[0])
    ident = tuple(range(n0))
    gens = [tuple(p) for p in perms]
    elems = {ident: 0}
    lst = [ident]
    i = 0
    while i < len(lst):
        g = lst[i]
        i += 1
        for p in gens:
            h = tuple(p[g[x]] for x in range(n0))  # g then p
            if h not in elems:
                elems[h] = len(lst)
                lst.append(h)
        if len(lst) > 200:
            return None
    out = []
    for p in gens:
        out.append([elems[tuple(p[g[x]] for x in range(n0))] for g in lst])
    return out


def fi_subgroup(words, perms):
    """Stabiliser of point 0 in the action of <words> via perms: graph."""
    n = len(perms[0])
    sedges = [(x, i, perms[i][x]) for i in range(len(perms)) for x in range(n)]
    return subst_graph(n, sedges, words)


# ------------------------------------------------------- relative rank <= 1

def relrank_le1(nx, Ex, ny, Ey, cy=None):
    """Exact: is Y = <X, h> for some h (X <= Y)?  Returns 'eq'|'arc'|'pair'|None."""
    if cy is None:
        cy = canon(ny, Ey)
    if canon(nx, Ex) == cy:
        return 'eq'
    if rank(ny, Ey) == rank(nx, Ex) + 1 and embeds(nx, Ex, ny, Ey):
        return 'arc'
    m = image_map(nx, Ex, ny, Ey)
    fib = {}
    for v, im in m.items():
        fib.setdefault(im, []).append(v)
    for vs in fib.values():
        for i in range(len(vs)):
            for k in range(i + 1, len(vs)):
                mm, F, _ = fold(nx, Ex, [(vs[i], vs[k])])
                if canon(mm, F) == cy:
                    return 'pair'
    return None


def cgraph(n, E):
    """Canonical relabelled core graph (n, edges) from canon."""
    c = canon(n, E)
    return c[0], list(c[1])


# ---------------------------------------------------------------- hosts

def phij(w, j):
    for _ in range(j):
        w = phi(w)
    return w


def rand_malnormal_rank2(rng, Lmin=3, Lmax=7, want=True):
    """Random rank-2 B = <u, v>, malnormal (want=True) or not (want=False),
    infinite index, u, v a free basis (rank of graph = 2)."""
    while True:
        u = rand_word(rng.randint(Lmin, Lmax), rng)
        v = rand_word(rng.randint(Lmin, Lmax), rng)
        n, E = compact(*graph_of([u, v]))
        if rank(n, E) != 2:
            continue
        # infinite index: not a covering (some vertex misses a label)
        full = all(sum(1 for e in E if e[0] == x) == 2 and
                   sum(1 for e in E if e[2] == x) == 2 for x in range(n))
        if full:
            continue
        if is_malnormal(n, E) == want:
            return [u, v], (n, E)


def host(kind, rng):
    """Returns (basis words of B, graph of B, basis words of the sub-host C)."""
    if kind == 'rand':
        ws, g = rand_malnormal_rank2(rng)
        return ws, g, ws
    if kind == 'nonmal':
        ws, g = rand_malnormal_rank2(rng, want=False)
        return ws, g, ws
    if kind == 'L1':
        ws = ['a', phij('b', 1)]
        return ws, compact(*graph_of(ws)), ws
    if kind == 'L2':
        ws = ['a', phij('b', 2)]
        return ws, compact(*graph_of(ws)), ws
    if kind == 'L1overL2':
        ws = ['a', phij('b', 1)]
        return ws, compact(*graph_of(ws)), ['a', phij('b', 2)]
    if kind == 'L2overL3':
        ws = ['a', phij('b', 2)]
        return ws, compact(*graph_of(ws)), ['a', phij('b', 3)]
    raise ValueError(kind)


def rand_X(Cws, rng, nmax=6, regular_prob=0.4):
    """Finite-index X in C = <Cws>: point stabiliser of a random transitive
    action, or a kernel (regular action) of a small random quotient."""
    while True:
        if rng.random() < regular_prob:
            m = rng.randint(3, 5)
            perms = [list(range(m)), list(range(m))]
            rng.shuffle(perms[0])
            rng.shuffle(perms[1])
            reg = regular_action(perms)
            if reg is None or len(reg[0]) < 3 or len(reg[0]) > 24:
                continue
            return fi_subgroup(Cws, reg), ('reg', len(reg[0]), perms)
        n = rng.randint(2, nmax)
        perms = rand_transitive_action(2, n, rng)
        return fi_subgroup(Cws, perms), ('perm', n, perms)


# ---------------------------------------------------------------- k = 1

def k1_instance(Bg, Xg, stats, tag, verbose=True):
    nB, EB = Bg
    nx, Ex = Xg
    cx = canon(nx, Ex)
    cB = canon(nB, EB)
    seen = set()
    viol = []
    for u in range(nx):
        for w in range(u + 1, nx):
            m, F, _ = fold(nx, Ex, [(u, w)])
            c = canon(m, F)
            if c in seen:
                continue
            seen.add(c)
            stats['J'] += 1
            ny, Ey = compact(*pullback(m, F, nB, EB))
            cy = canon(ny, Ey)
            if cy == cx:
                continue
            stats['Yneq'] += 1
            if cy == cB:
                stats['YB'] += 1
            r = relrank_le1(nx, Ex, ny, Ey, cy)
            stats[r] = stats.get(r, 0) + 1
            if r is None:
                stats['viol'] += 1
                viol.append((u, w))
                if verbose:
                    print('K1-VIOLATION %s pair=(%d,%d) rkX=%d rkJ=%d rkY=%d YB=%s'
                          % (tag, u, w, rank(nx, Ex), rank(m, F), rank(ny, Ey),
                             cy == cB), flush=True)
    return viol


def run_k1(seed, T, kind):
    rng = random.Random(seed)
    stats = dict(inst=0, J=0, Yneq=0, YB=0, viol=0)
    for t in range(T):
        Bws, Bg, Cws = host(kind, rng)
        Xg, desc = rand_X(Cws, rng)
        if Xg[0] > 160:
            continue
        stats['inst'] += 1
        tag = 'B=%s C=%s X=%s' % (Bws, Cws, desc)
        k1_instance(Bg, Xg, stats, tag)
        if stats['inst'] % 25 == 0:
            print('progress k1', kind, 'seed', seed, stats, flush=True)
    print('k1', kind, 'seed', seed, stats, flush=True)


def selftest():
    # w19-fp-last1: B = <b, c>, c = a b^2 a^-1; X = ker(B -> S3), b->(123), c->(12)
    Bws = ['b', 'abbA']
    Bg = compact(*graph_of(Bws))
    print('nonmal host malnormal?', is_malnormal(*Bg))
    print('L1 malnormal?', is_malnormal(*compact(*graph_of(['a', phi('b')]))))
    print('L2 malnormal?', is_malnormal(*compact(*graph_of(['a', phij('b', 2)]))))
    print('<a, bab^-1> malnormal?', is_malnormal(*compact(*graph_of(['a', 'baB']))))
    reg = regular_action([[1, 2, 0], [1, 0, 2]])
    Xg = fi_subgroup(Bws, reg)
    print('|S3| =', len(reg[0]), 'rk X =', rank(*Xg))
    stats = dict(inst=1, J=0, Yneq=0, YB=0, viol=0)
    v = k1_instance(Bg, Xg, stats, 'selftest', verbose=False)
    print('selftest stats', stats, 'violations', len(v))



# ---------------------------------------------------------------- k = 2

def attach_arc(nx, Ex, x1, x2, sigma):
    """Gamma_X with a new path labelled sigma from x1 to x2; folded, core."""
    N = nx
    E = list(Ex)
    cur = x1
    if not sigma:
        m, F, _ = fold(nx, Ex, [(x1, x2)])
        return compact(m, F)
    for t, c in enumerate(sigma):
        nxt = x2 if t == len(sigma) - 1 else N
        if t < len(sigma) - 1:
            N += 1
        if c in 'ab':
            E.append((cur, c, nxt))
        else:
            E.append((nxt, c.lower(), cur))
        cur = nxt
    m, F, _ = fold(N, E)
    return compact(m, F)


def paths_in(ny, Ey, start, L):
    """All reduced paths of length 1..L from start in Gamma_Y: (word, end)."""
    adj = {}
    for (u, l, v) in Ey:
        adj.setdefault(u, []).append((l, v))
        adj.setdefault(v, []).append((l.upper(), u))
    out = []
    stack = [('', start)]
    while stack:
        w, v = stack.pop()
        if w:
            out.append((w, v))
        if len(w) == L:
            continue
        for (c, t) in adj.get(v, []):
            if w and w[-1] == INV[c]:
                continue
            stack.append((w + c, t))
    return out


def relrank_le2(nx, Ex, ny, Ey, cy, L, xs_max=12):
    """Semi-decision for rk(Y : X) <= 2.  Returns a certificate string or None."""
    r = relrank_le1(nx, Ex, ny, Ey, cy)
    if r is not None:
        return 'le1:' + r
    m = image_map(nx, Ex, ny, Ey)
    fib = {}
    for v, im in m.items():
        fib.setdefault(im, []).append(v)
    tried = set()
    # Z = one-pair fold of Gamma_X inside Y
    for vs in fib.values():
        for i in range(len(vs)):
            for k in range(i + 1, len(vs)):
                mm, F, _ = fold(nx, Ex, [(vs[i], vs[k])])
                Zg = compact(mm, F)
                cz = canon(*Zg)
                if cz in tried:
                    continue
                tried.add(cz)
                if relrank_le1(Zg[0], Zg[1], ny, Ey, cy) is not None:
                    return 'pair+1'
    # Z = <X, h>, h an arc sigma from x1 to x2 (immersed path of Gamma_Y)
    rng = random.Random(1)
    verts = list(range(nx))
    rng.shuffle(verts)
    for x1 in [0] + verts[:xs_max]:
        for (sigma, end) in paths_in(ny, Ey, m[x1], L):
            for x2 in fib.get(end, []):
                Zg = attach_arc(nx, Ex, x1, x2, sigma)
                cz = canon(*Zg)
                if cz in tried:
                    continue
                tried.add(cz)
                if relrank_le1(Zg[0], Zg[1], ny, Ey, cy) is not None:
                    return 'arc(%d)+1' % len(sigma)
    return None


ARCPAIR = False


def run_k2(seed, T, kind, S, L=6):
    rng = random.Random(seed)
    stats = dict(inst=0, J=0, Yneq=0, YB=0, gt1=0, cand=0)
    certs = {}
    for t in range(T):
        Bws, Bg, Cws = host(kind, rng)
        Xg, desc = rand_X(Cws, rng)
        nx, Ex = Xg
        if nx > 120 or nx < 3:
            continue
        stats['inst'] += 1
        nB, EB = Bg
        cx = canon(nx, Ex)
        cB = canon(nB, EB)
        seen = set()
        for s in range(S):
            if ARCPAIR:
                # arc sigma from x1 to x2 (new interior vertices), then one pair
                # (interior arc vertex, vertex of Gamma_X): the infinite family
                x1, x2 = rng.randrange(nx), rng.randrange(nx)
                sigma = rand_word(rng.randint(2, 8), rng)
                N = nx
                EE = list(Ex)
                cur = x1
                for t_, c_ in enumerate(sigma):
                    nxt = x2 if t_ == len(sigma) - 1 else N
                    if t_ < len(sigma) - 1:
                        N += 1
                    if c_ in 'ab':
                        EE.append((cur, c_, nxt))
                    else:
                        EE.append((nxt, c_.lower(), cur))
                    cur = nxt
                pi = rng.randrange(nx, N)
                px = rng.randrange(nx)
                p = (x1, sigma, x2, pi - nx, px)
                mJ, FJ, _ = fold(N, EE, [(pi, px)])
            else:
                p = rng.sample(range(nx), 4)
                mJ, FJ, _ = fold(nx, Ex, [(p[0], p[1]), (p[2], p[3])])
            c = canon(mJ, FJ)
            if c in seen:
                continue
            seen.add(c)
            stats['J'] += 1
            ny, Ey = compact(*pullback(mJ, FJ, nB, EB))
            cy = canon(ny, Ey)
            if cy == cx:
                continue
            stats['Yneq'] += 1
            if cy == cB:
                stats['YB'] += 1
            if relrank_le1(nx, Ex, ny, Ey, cy) is not None:
                continue
            stats['gt1'] += 1
            cert = relrank_le2(nx, Ex, ny, Ey, cy, L)
            key = cert.split(':')[0] if cert else None
            certs[key] = certs.get(key, 0) + 1
            if cert is None:
                stats['cand'] += 1
                print('K2-CANDIDATE B=%s C=%s X=%s pairs=%s rkX=%d rkJ=%d rkY=%d YB=%s'
                      % (Bws, Cws, desc, p, rank(nx, Ex), rank(mJ, FJ),
                         rank(ny, Ey), cy == cB), flush=True)
        if stats['inst'] % 10 == 0:
            print('progress k2', kind, 'seed', seed, stats, 'certs', certs, flush=True)
    print('k2', kind, 'seed', seed, stats, 'certs', certs, flush=True)


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'selftest':
        selftest()
    elif mode == 'k1':
        run_k1(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    elif mode in ('k2', 'k2arc'):
        ARCPAIR = (mode == 'k2arc')
        run_k2(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5]))
