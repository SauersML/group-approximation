"""Permutation helpers. A permutation is a tuple p with p[x] the image of x.
Composition mul(P, Q)[x] = P[Q[x]] (left actions), so relators are read as matrices."""
from collections import deque


def mul(*ps):
    r = ps[-1]
    for p in reversed(ps[:-1]):
        r = tuple(p[x] for x in r)
    return r


def inv(p):
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return tuple(q)


def ident(n):
    return tuple(range(n))


def comm(p, q):
    return mul(p, q, inv(p), inv(q))


def power(p, e):
    if e < 0:
        p, e = inv(p), -e
    r = ident(len(p))
    for _ in range(e):
        r = mul(p, r)
    return r


def perm_rank_defect(p):
    """rank(P - I) over Q for a permutation matrix P: moved points minus nontrivial cycles."""
    n = len(p)
    seen = [False] * n
    moved = cycles = 0
    for x in range(n):
        if seen[x] or p[x] == x:
            seen[x] = True
            continue
        cycles += 1
        y = x
        while not seen[y]:
            seen[y] = True
            moved += 1
            y = p[y]
    return moved - cycles


def transitive(gens):
    n = len(gens[0])
    seen = {0}
    dq = deque([0])
    while dq:
        x = dq.popleft()
        for g in gens:
            y = g[x]
            if y not in seen:
                seen.add(y)
                dq.append(y)
    return len(seen) == n


def isos(G, H, start=0, targets=None):
    """All bijections f with f G_i = H_i f (G transitive). Yields f as tuple."""
    n = len(G[0])
    Gi = [inv(g) for g in G]
    Hi = [inv(h) for h in H]
    for t in (range(n) if targets is None else targets):
        f = [-1] * n
        used = [False] * n
        f[start] = t
        used[t] = True
        dq = deque([start])
        ok = True
        while dq and ok:
            x = dq.popleft()
            for g, h in list(zip(G, H)) + list(zip(Gi, Hi)):
                y, fy = g[x], h[f[x]]
                if f[y] == -1:
                    if used[fy]:
                        ok = False
                        break
                    f[y] = fy
                    used[fy] = True
                    dq.append(y)
                elif f[y] != fy:
                    ok = False
                    break
        if ok and all(v >= 0 for v in f):
            yield tuple(f)


def relators(b, c, s, t):
    """Relators of Z^2 x| SL_2(Z) with S=[[0,-1],[1,0]], T=[[1,1],[0,1]] acting on b=e1, c=e2."""
    I = ident(len(b))
    return {
        "[b,c]": comm(b, c),
        "tbt^-1b^-1": mul(t, b, inv(t), inv(b)),
        "tct^-1(bc)^-1": mul(t, c, inv(t), inv(mul(b, c))),
        "sbs^-1c^-1": mul(s, b, inv(s), inv(c)),
        "scs^-1b": mul(s, c, inv(s), b),
        "s^4": power(s, 4),
        "s^2(st)^-3": mul(s, s, inv(power(mul(s, t), 3))),
    }
