"""Prefix-table arithmetic in V_(h,2)(<odometer>) and the arithmetic
near group G=<lambda(A*A), s> for a finite group A with h=|A|-1.

Points: (root, d1, d2, ...) with root in {0,1}, digits in 1..h.
Odometer a on digits: a(d w)=(d+1) w for d<h, a(h w)=1 a(w).
An element is a dict {u: (v, k)} over a complete prefix code of
cones u (tuples starting with a root), meaning u.w -> v.a^k(w).
"""
import itertools, random, sys


def odo(word, k, h):
    """a^k(word . t) = word' . a^k'(t); return (word', k')."""
    out = []
    c = k
    for d in word:
        t = d - 1 + c
        out.append(t % h + 1)
        c = t // h
    return tuple(out), c


def split_leaf(u, v, k, h):
    return {u + (d,): (v + ((d - 1 + k) % h + 1,), (d - 1 + k) // h)
            for d in range(1, h + 1)}


def reduce_table(T, h):
    T = dict(T)
    changed = True
    while changed:
        changed = False
        parents = {}
        for u in T:
            if len(u) > 1:
                parents.setdefault(u[:-1], []).append(u)
        for p, kids in parents.items():
            if len(kids) != h:
                continue
            if not all(p + (d,) in T for d in range(1, h + 1)):
                continue
            v1, k1 = T[p + (1,)]
            if len(v1) < 2:
                continue
            e1 = v1[-1]
            k = k1 * h + (e1 - 1)
            v = v1[:-1]
            if all(T[p + (d,)] == (v + ((d - 1 + k) % h + 1,), (d - 1 + k) // h)
                   for d in range(1, h + 1)):
                for d in range(1, h + 1):
                    del T[p + (d,)]
                T[p] = (v, k)
                changed = True
    return T


def find_leaf(T, x):
    """leaf of T whose cone contains prefix x or None (x too short)."""
    for L in range(1, len(x) + 1):
        if x[:L] in T:
            return x[:L]
    return None


def compose(F, G, h):
    """F after G."""
    out = {}
    stack = list(G.items())
    while stack:
        u, (v, k) = stack.pop()
        x = find_leaf(F, v)
        if x is None:
            stack.extend(split_leaf(u, v, k, h).items())
            continue
        y, j = F[x]
        z = v[len(x):]
        z2, j2 = odo(z, j, h)
        out[u] = (y + z2, k + j2)
    return reduce_table(out, h)


def inverse(F, h):
    return reduce_table({v: (u, -k) for u, (v, k) in F.items()}, h)


IDENT = {(0,): ((0,), 0), (1,): ((1,), 0)}


def is_id(F):
    return F == IDENT


def cyclic_group(n):
    elems = list(range(n))
    mul = lambda a, b: (a + b) % n
    return elems, 0, mul


def make_generators(n=None, group=None):
    if group is None:
        elems, e, mul = cyclic_group(n)
    else:
        elems, e, mul = group
    non = [x for x in elems if x != e]
    h = len(non)
    idx = {x: i + 1 for i, x in enumerate(non)}
    gens = {}
    for r in (0, 1):
        o = 1 - r
        for a in non:
            T = {(o,): ((r, idx[a]), 0)}
            for x in non:
                ax = mul(a, x)
                T[(r, idx[x])] = ((o,), 0) if ax == e else ((r, idx[ax]), 0)
            gens[(r, a)] = reduce_table(T, h)
    s = {(0,): ((1,), 0), (1,): ((0,), 1)}
    return h, gens, s


def charge(F):
    return sum(k for (_, k) in F.values())


def support_measure(F, h):
    m = 0.0
    for u, (v, k) in F.items():
        if not (u == v and k == 0):
            m += 0.5 * h ** (-(len(u) - 1))
    return m


def power(F, n, h):
    R = IDENT
    base = F if n >= 0 else inverse(F, h)
    for _ in range(abs(n)):
        R = compose(base, R, h)
    return R


def comm(F, G, h):
    return compose(compose(F, G, h), compose(inverse(F, h), inverse(G, h), h), h)


def fmt(F):
    return "; ".join(f"{''.join(map(str,u))}->{''.join(map(str,v))}[{k}]"
                     for u, (v, k) in sorted(F.items()))
