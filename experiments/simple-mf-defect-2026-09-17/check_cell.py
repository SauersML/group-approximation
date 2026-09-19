"""Exact check of the compression cell in P = FAlt(Z x {1,2}) semidirect <u, sigma>.

Points of Omega are pairs (n, i), n an integer, i in {1, 2}.
  u     : (n,1) -> (n+1,1),  (n,2) -> (n-1,2)
  sigma : (n,i) -> (n,3-i)
Finitary permutations are dicts on their support.  Composition is right to
left: (g*h)(x) = g(h(x)).

Checks, all exact:
  1. sigma u sigma^-1 = u^-1 on a window, hence [sigma,u] = u^-2.
  2. c = (-4,-3,-2) and l = (0,1,2), both on copy 1, are even permutations,
     and for k = 0..K the conjugate u^{2k} l u^{-2k} commutes with c
     (these conjugates have support {2k,2k+1,2k+2} x {1}, disjoint from supp c
     for every k >= 0; K is only a sanity bound, disjointness is the proof).
  3. delta = [u^2 c u^-2, l] is a nontrivial even permutation of
     {-2,...,2} x {1}, and it is not central in Alt of that set.
"""

from itertools import permutations


def u(p, k=1):
    n, i = p
    return (n + k, 1) if i == 1 else (n - k, 2)


def sigma(p):
    n, i = p
    return (n, 3 - i)


def cycle(pts):
    return {pts[j]: pts[(j + 1) % len(pts)] for j in range(len(pts))}


def app(g, x):
    return g.get(x, x)


def mul(g, h):
    keys = set(g) | set(h)
    out = {x: app(g, app(h, x)) for x in keys}
    return {x: y for x, y in out.items() if x != y}


def inv(g):
    return {y: x for x, y in g.items()}


def comm(g, h):
    return mul(mul(g, h), mul(inv(g), inv(h)))


def conj_u(g, k):
    """u^k g u^-k."""
    return {u(x, k): u(y, k) for x, y in g.items()}


def sign(g):
    seen, s = set(), 1
    for x in g:
        if x in seen:
            continue
        length, y = 0, x
        while y not in seen:
            seen.add(y)
            y = app(g, y)
            length += 1
        if length % 2 == 0:
            s = -s
    return s


def main():
    window = [(n, i) for n in range(-50, 51) for i in (1, 2)]
    # 1. sigma u sigma^-1 = u^-1
    assert all(sigma(u(sigma(x))) == u(x, -1) for x in window)
    # [sigma,u] = sigma u sigma^-1 u^-1 = u^-1 u^-1 = u^-2
    assert all(sigma(u(sigma(u(x, -1)))) == u(x, -2) for x in window)

    c = cycle([(-4, 1), (-3, 1), (-2, 1)])
    l = cycle([(0, 1), (1, 1), (2, 1)])
    assert sign(c) == 1 and sign(l) == 1
    for k in range(0, 200):
        lk = conj_u(l, 2 * k)
        assert set(lk).isdisjoint(set(c))
        assert comm(c, lk) == {}

    uc = conj_u(c, 2)
    assert uc == cycle([(-2, 1), (-1, 1), (0, 1)])
    delta = comm(uc, l)
    assert delta != {} and sign(delta) == 1
    five = [(n, 1) for n in range(-2, 3)]
    assert set(delta) <= set(five)

    # delta is not central in Alt(five): find an even permutation not commuting.
    witness = None
    for perm in permutations(five):
        g = {five[j]: perm[j] for j in range(5) if five[j] != perm[j]}
        if sign(g) == 1 and comm(g, delta) != {}:
            witness = g
            break
    assert witness is not None
    print("cell verified: delta =", sorted(delta.items()))


if __name__ == "__main__":
    main()
