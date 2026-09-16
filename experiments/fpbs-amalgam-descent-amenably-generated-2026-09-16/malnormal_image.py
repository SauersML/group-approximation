#!/usr/bin/env python3
"""Search for u, v in F_2 = <a, b> such that H = <u, v> is a proper, rank-2,
malnormal subgroup, certified by Stallings folding.

Exact checks (no floating point, no randomness):
  * fold(): Stallings folding of the bouquet of the petals u, v.  The folded
    graph is the (based) Stallings graph of H; it is unique for H.
  * rank(H) = E - V + 1 of the folded graph.
  * H = F_2 iff the folded graph is one vertex with an a-loop and a b-loop.
  * Malnormality certificate: every connected component of the product
    (pullback) graph G x G that contains an off-diagonal vertex (x, y), x != y,
    is a tree (E = V - 1).  This is sufficient (not necessary) for
    malnormality; the proof is Lemma 5.2 of
    research/artifacts/fpbs-amalgam-descent-amenably-generated-2026-09-16.md.
Letters: a, b, and A = a^-1, B = b^-1.  Run: python3 malnormal_image.py [maxlen]
"""
import itertools
import sys

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def reduced(w):
    return all(w[i + 1] != INV[w[i]] for i in range(len(w) - 1))


def fold(words):
    # vertices are ints; edges stored as set of (p, x, q) with x in {'a','b'}
    edges = set()
    nv = 1
    for w in words:
        cur = 0
        for i, ch in enumerate(w):
            nxt = 0 if i == len(w) - 1 else nv
            if nxt != 0:
                nv += 1
            if ch in 'ab':
                edges.add((cur, ch, nxt))
            else:
                edges.add((nxt, ch.lower(), cur))
            cur = nxt
    parent = list(range(nv))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    changed = True
    while changed:
        changed = False
        edges = {(find(p), x, find(q)) for (p, x, q) in edges}
        out, inn = {}, {}
        for (p, x, q) in edges:
            for key, tgt, table in (((p, x), q, out), ((q, x), p, inn)):
                if key in table and find(table[key]) != find(tgt):
                    r1, r2 = find(table[key]), find(tgt)
                    parent[max(r1, r2)] = min(r1, r2)
                    changed = True
                else:
                    table.setdefault(key, tgt)
    verts = {find(0)} | {p for (p, _, _) in edges} | {q for (_, _, q) in edges}
    return verts, edges, find(0)


def components(verts, edges):
    adj = {v: set() for v in verts}
    for (p, _, q) in edges:
        adj[p].add(q)
        adj[q].add(p)
    seen, comps = set(), []
    for v in verts:
        if v in seen:
            continue
        stack, comp = [v], {v}
        seen.add(v)
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    comp.add(y)
                    stack.append(y)
        comps.append(comp)
    return comps


def certify(u, v):
    verts, edges, base = fold([u, v])
    V, E = len(verts), len(edges)
    rank = E - V + 1
    is_whole = (V == 1 and E == 2)
    pverts = {(x, y) for x in verts for y in verts}
    pedges = {((p1, p2), a, (q1, q2))
              for (p1, a, q1) in edges for (p2, b, q2) in edges if a == b}
    ok = True
    for comp in components(pverts, pedges):
        if all(x == y for (x, y) in comp):
            continue  # the diagonal component consists of diagonal vertices
        ce = sum(1 for (p, _, q) in pedges if p in comp)
        if ce != len(comp) - 1:
            ok = False
            break
    return rank, is_whole, ok, V, E


def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    found = []
    for L in range(2, 2 * maxlen + 1):
        for lu in range(1, maxlen + 1):
            lv = L - lu
            if lv < lu or lv > maxlen:
                continue
            for u in map(''.join, itertools.product('abAB', repeat=lu)):
                if not reduced(u):
                    continue
                for v in map(''.join, itertools.product('abAB', repeat=lv)):
                    if not reduced(v):
                        continue
                    rank, whole, mal, V, E = certify(u, v)
                    if rank == 2 and not whole and mal:
                        found.append((u, v, V, E))
                        if len(found) >= 5:
                            for f in found:
                                print('u=%s v=%s folded V=%d E=%d rank=2 proper malnormal' % f)
                            return
    for f in found:
        print('u=%s v=%s folded V=%d E=%d rank=2 proper malnormal' % f)
    if not found:
        print('none found up to length', maxlen)


if __name__ == '__main__':
    # sanity checks of the certificate on known subgroups
    print('check <a,b>:', certify('a', 'b'))           # whole group
    print('check <a,bab^-1>:', certify('a', 'baB'))    # not malnormal
    print('check <a^2,b>:', certify('aa', 'b'))        # not malnormal (a^2 root)
    print('check <aba^-1,b^2> (T5):', certify('abA', 'bb'))
    main()
