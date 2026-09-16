#!/usr/bin/env python3
"""Search symmetric S in H_3(Z) whose Cayley clique complex is an affine
triangulation of R^3 = H_3(R).

H_3(Z) = {(a,b,c)}, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab'). Left
translation is affine in (a,b,c), so f(g) = (a,b,c) extends affinely and
equivariantly from Flag(Cay(H,S)) to R^3. The local test at vertex 1 is:
  L1  the link graph on S (s ~ s' iff s^-1 s' in S) has no 4-clique, so the
      flag complex is 3-dimensional;
  L2  its clique complex L is a closed connected surface with chi = 2 (every
      edge in exactly two triangles, every vertex link a single cycle);
  L3  every link triangle {s1,s2,s3} has det[f(s1),f(s2),f(s3)] != 0, and for
      every link edge {s,s'} the two opposite vertices lie on opposite sides
      of the plane spanned by f(s), f(s');
  L4  a generic ray from 0 meets exactly one open cone over a link triangle
      (degree 1).
L1-L4 make the radial projection L -> S^2 a homeomorphism, so f is a local
homeomorphism at 1, hence everywhere; see the notes/artifact for the covering
argument.  Usage: search_h3_rips.py [pairs] (default 7).
"""
import itertools, sys
from fractions import Fraction as Fr


def mul(g, h):
    return (g[0] + h[0], g[1] + h[1], g[2] + h[2] + g[0] * h[1])


def inv(g):
    return (-g[0], -g[1], -g[2] + g[0] * g[1])


def det3(u, v, w):
    return (u[0] * (v[1] * w[2] - v[2] * w[1]) - u[1] * (v[0] * w[2] - v[2] * w[0])
            + u[2] * (v[0] * w[1] - v[1] * w[0]))


RAYS = [(Fr(1000003), Fr(7919), Fr(104729)), (Fr(-3), Fr(1009), Fr(-2711)), (Fr(13), Fr(-1), Fr(-4099))]


def cone_contains(tri, v):
    # solve v = l1 u1 + l2 u2 + l3 u3; return (inside_open, on_boundary)
    u1, u2, u3 = tri
    D = det3(u1, u2, u3)
    l1, l2, l3 = det3(v, u2, u3) / D, det3(u1, v, u3) / D, det3(u1, u2, v) / D
    if min(l1, l2, l3) > 0:
        return True, False
    return False, (min(l1, l2, l3) == 0 and max(l1, l2, l3) > 0)


def test(S, verbose=False):
    Sset = set(S)
    adj = {s: {u for u in S if u != s and mul(inv(s), u) in Sset} for s in S}
    tris = [t for t in itertools.combinations(S, 3) if t[1] in adj[t[0]] and t[2] in adj[t[0]] and t[2] in adj[t[1]]]
    for t in tris:                                   # L1
        if adj[t[0]] & adj[t[1]] & adj[t[2]]:
            return False, 'L1: 4-clique in link'
    edges = [(s, u) for s in S for u in adj[s] if s < u]
    opp = {e: [] for e in edges}
    for t in tris:
        for i in range(3):
            e = tuple(sorted((t[i], t[(i + 1) % 3])))
            opp[e].append(t[(i + 2) % 3])
    if any(len(o) != 2 for o in opp.values()):       # L2 pseudomanifold
        return False, 'L2: edge not in exactly two triangles'
    for s in S:                                      # L2 vertex links are cycles
        nb = adj[s]
        if not nb:
            return False, 'L2: isolated vertex'
        start = next(iter(nb)); seen = {start}; stack = [start]
        while stack:
            u = stack.pop()
            for w in adj[u] & nb:
                if w not in seen:
                    seen.add(w); stack.append(w)
        if seen != nb or any(len(adj[u] & nb) != 2 for u in nb):
            return False, 'L2: vertex link not a cycle'
    chi = len(S) - len(edges) + len(tris)
    comp = {S[0]}; stack = [S[0]]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in comp:
                comp.add(w); stack.append(w)
    if chi != 2 or len(comp) != len(S):
        return False, f'L2: chi={chi}, connected={len(comp)==len(S)}'
    for t in tris:                                   # L3
        if det3(*t) == 0:
            return False, 'L3: degenerate tetrahedron'
    for (s, u), (p, q) in opp.items():
        if (det3(s, u, p) > 0) == (det3(s, u, q) > 0):
            return False, 'L3: fold across a link edge'
    for v in RAYS:                                   # L4
        hits, bdry = 0, False
        for t in tris:
            ins, b = cone_contains(t, v)
            hits += ins; bdry |= b
        if not bdry:
            if hits != 1:
                return False, f'L4: degree {hits}'
            if verbose:
                print('  link: V=%d E=%d F=%d, degree 1 along ray %s' % (len(S), len(edges), len(tris), v))
            return True, 'ok'
    return False, 'L4: no generic ray found'


def verify_chosen():
    import random
    x, y, z = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    reps = [x, y, z, mul(x, z), mul(y, z), mul(x, y), mul(mul(x, y), z)]
    S = sorted(set(reps) | {inv(g) for g in reps})
    print('S+ = x, y, z, xz, yz, xy, xyz =', reps)
    assert len(S) == 14
    ok, why = test(S, verbose=True)
    print('L1-L4:', ok, why)
    assert ok
    Sset = set(S)
    tris = [t for t in itertools.combinations(S, 3)
            if all(mul(inv(u), w) in Sset for u, w in itertools.combinations(t, 2))]
    print('link triangles (%d), as coordinates (a,b,c):' % len(tris))
    for t in tris:
        print('  ', t, 'det', det3(*t))
    # independent sanity check: random rational directions lie in exactly one
    # open cone (or on a boundary, which is then skipped)
    rng = random.Random(7); counted = 0
    for _ in range(2000):
        v = tuple(Fr(rng.randint(-10**6, 10**6), rng.randint(1, 997)) for _ in range(3))
        if v == (0, 0, 0):
            continue
        res = [cone_contains(t, v) for t in tris]
        if any(b for _, b in res):
            continue
        assert sum(i for i, _ in res) == 1, v
        counted += 1
    print('random directions in exactly one cone:', counted, 'of', counted)


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'verify':
        verify_chosen(); sys.exit(0)
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    B = [(a, b, c) for a in (-1, 0, 1) for b in (-1, 0, 1) for c in range(-2, 3) if (a, b, c) != (0, 0, 0)]
    pairs = sorted({tuple(sorted((g, inv(g)))) for g in B if inv(g) in B})
    print('pool of inverse pairs:', len(pairs))
    found = []
    for combo in itertools.combinations(pairs, p):
        S = sorted({x for pr in combo for x in pr})
        gens = {g[:2] for g in S}
        if not ({(1, 0), (-1, 0)} & gens and {(0, 1), (0, -1)} & gens):
            pass
        ok, why = test(S)
        if ok:
            found.append(S)
    print('pairs=%d: %d generating sets pass L1-L4' % (p, len(found)))
    for S in found[:10]:
        print(' ', [x for x in S if x > inv(x) or x == max(x, inv(x))])
