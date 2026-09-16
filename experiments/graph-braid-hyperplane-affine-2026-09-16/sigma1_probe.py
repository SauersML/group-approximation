#!/usr/bin/env python3
"""Probe the m = 1 case of the ascending-matching-complex criterion on UD_2 Gamma.

For n = 2 and a subdivided graph Gamma, a generic hyperplane-affine cocycle is
a sign pattern s : {hyperplane classes} -> {+1, -1} (only signs matter for the
criterion).  At a configuration S = {v, v'} the ascending link is the graph
whose vertices are ascending moves (particle p -> free neighbour w along an
edge e of Gamma) and whose edges join two moves of different particles with
different targets (they span a square).  The m = 1 criterion of
`graph-braid-ascending-matching-complexes-give-sigma` asks that every
ascending link be nonempty and connected.

The script searches all sign patterns by backtracking and prints how many
satisfy the criterion (up to a cap) and one witness.

Sanity expectations: free groups (trees, K_4, Theta_3 at n = 2) have
Sigma^1 = empty, so no pattern should pass there; the cycle (B_2 = Z) should
pass.  This is evidence only.  Single-threaded, small inputs only.
"""
import itertools, sys
from hyperplane_affine import GRAPHS, subdivide

CAP = 1000


def build(nv, gedges):
    # X-edges (z, ei): particle parked at z, the other particle moves along ei = (a, b)
    E = []
    eidx = {}
    for ei, (a, b) in enumerate(gedges):
        for z in range(nv):
            if z != a and z != b:
                eidx[(z, ei)] = len(E)
                E.append((z, ei))
    parent = list(range(len(E)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for ei, fi in itertools.combinations(range(len(gedges)), 2):
        a, b = gedges[ei]
        c, d = gedges[fi]
        if len({a, b, c, d}) < 4:
            continue
        for x, y in ((eidx[(c, ei)], eidx[(d, ei)]), (eidx[(a, fi)], eidx[(b, fi)])):
            rx, ry = find(x), find(y)
            if rx != ry:
                parent[rx] = ry
    roots = sorted({find(x) for x in range(len(E))})
    cls = {r: i for i, r in enumerate(roots)}
    klass = [cls[find(x)] for x in range(len(E))]
    # configurations and their moves: (particle, target, class, orientation)
    configs = []
    for v, vp in itertools.combinations(range(nv), 2):
        moves = []
        for ei, (a, b) in enumerate(gedges):
            for p, w, o in ((a, b, 1), (b, a, -1)):
                other = vp if p == v else (v if p == vp else None)
                if other is None or w == other:
                    continue
                moves.append((p, w, klass[eidx[(other, ei)]], o))
        configs.append(((v, vp), moves))
    return len(roots), configs


def collapses_to_graph(gedges):
    """Repeatedly delete a square of UD_2 Gamma having a free edge (an edge in
    no other remaining square).  True iff all squares go, in which case UD_2
    Gamma is homotopy equivalent to a graph and B_2 Gamma is free.  (False is
    inconclusive in principle.)"""
    sq = []
    for ei, fi in itertools.combinations(range(len(gedges)), 2):
        a, b = gedges[ei]
        c, d = gedges[fi]
        if len({a, b, c, d}) < 4:
            continue
        sq.append(((c, ei), (d, ei), (a, fi), (b, fi)))
    alive = set(range(len(sq)))
    cnt = {}
    for i in alive:
        for x in sq[i]:
            cnt[x] = cnt.get(x, 0) + 1
    progress = True
    while progress:
        progress = False
        for i in list(alive):
            if any(cnt[x] == 1 for x in sq[i]):
                alive.discard(i)
                for x in sq[i]:
                    cnt[x] -= 1
                progress = True
    return len(alive) == 0


def link_ok(moves, sign):
    asc = [(p, w) for (p, w, k, o) in moves if sign[k] * o > 0]
    if not asc:
        return False
    # connectivity: vertices asc, edges between different particles and targets
    seen = {0}
    stack = [0]
    while stack:
        i = stack.pop()
        pi, wi = asc[i]
        for j, (pj, wj) in enumerate(asc):
            if j not in seen and pj != pi and wj != wi:
                seen.add(j)
                stack.append(j)
    return len(seen) == len(asc)


def search(H, configs):
    # order classes by first appearance; attach each config to the depth at which
    # its last class gets assigned
    order = []
    pos = {}
    for (_, moves) in configs:
        for (_, _, k, _) in moves:
            if k not in pos:
                pos[k] = len(order)
                order.append(k)
    for k in range(H):
        if k not in pos:
            pos[k] = len(order)
            order.append(k)
    checks = [[] for _ in range(H)]
    for (S, moves) in configs:
        d = max((pos[k] for (_, _, k, _) in moves), default=None)
        if d is None:
            return 0, None  # a configuration with no moves: link empty
        checks[d].append(moves)
    sign = [0] * H
    count = 0
    witness = None

    def rec(d):
        nonlocal count, witness
        if count >= CAP:
            return
        if d == H:
            count += 1
            if witness is None:
                witness = list(sign)
            return
        k = order[d]
        for s in (1, -1):
            sign[k] = s
            if all(link_ok(m, sign) for m in checks[d]):
                rec(d + 1)
        sign[k] = 0

    sys.setrecursionlimit(10000)
    rec(0)
    return count, witness


if __name__ == '__main__':
    # usage: sigma1_probe.py <graph> [k | l1,l2,...]      (n = 2 only)
    name = sys.argv[1]
    if len(sys.argv) > 2 and ',' in sys.argv[2]:
        k = [int(t) for t in sys.argv[2].split(',')]
    else:
        k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    nv, ge = subdivide(GRAPHS[name], k)
    H, configs = build(nv, ge)
    count, witness = search(H, configs)
    print(name, 'n=2', 'k=%s' % (k,), 'classes=%d' % H,
          'collapses_to_graph=%s' % collapses_to_graph(ge),
          'passing_sign_patterns=%s' % (('>=%d' % CAP) if count >= CAP else count),
          'witness=%s' % (witness,))
