"""Export a depth-j overfold instance for the C solver deep.c.

Usage: python3 export.py j a-perm b-perm [cayley] > inst.txt
With 'cayley', (a-perm, b-perm) generate a permutation group and Q is its
right-regular (Cayley) action, as in struct_search.cayley.

Output format (whitespace separated):
  V n
  V lines: nb[v][a+] nb[v][a-] nb[v][b+] nb[v][b-]   (-1 if absent)
  V ints: m[v]            (vertex of Gamma_j(Q))
  V ints: over[v]         (point of Q)
  S
  S lines: u v lawful(0/1)   one representative per single-seed closure class
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-relative-rank-2026-09-17'))
from foldlib import depth_graphs  # noqa: E402
from struct_search import cayley, seeds_of  # noqa: E402

KEYS = [('a', 1), ('a', -1), ('b', 1), ('b', -1)]


def instance_text(PA, PB, j):
    Gj, G, m = depth_graphs(PA, PB, j)
    allp, lawp = seeds_of(G, m)
    law = set(map(tuple, lawp))
    out = [f"{G.V} {len(PA)}"]
    for v in range(G.V):
        out.append(' '.join(str(G.nb[v].get(k, -1)) for k in KEYS))
    out.append(' '.join(str(x) for x in m))
    out.append(' '.join(str(x) for x in G.over))
    # lawful classes get their lawful representative; a class may then be
    # listed twice (same closure), which is harmless for the search
    reps = [tuple(p) for p in lawp] + [tuple(p) for p in allp if tuple(p) not in law]
    out.append(str(len(reps)))
    for (u, v) in reps:
        out.append(f"{u} {v} {1 if m[u] == m[v] else 0}")
    # automorphisms of the L-set Q, lifted to G by reading BFS words
    n = len(PA)
    auts = []
    for img0 in range(n):
        sig = {0: img0}
        stack = [0]
        ok = True
        while stack and ok:
            p = stack.pop()
            for P in (PA, PB):
                q, q2 = P[p], P[sig[p]]
                if q in sig:
                    ok = ok and sig[q] == q2
                else:
                    sig[q] = q2
                    stack.append(q)
            for P in (PA, PB):
                inv_ = {P[x]: x for x in range(n)}
                q, q2 = inv_[p], inv_[sig[p]]
                if q in sig:
                    ok = ok and sig[q] == q2
                else:
                    sig[q] = q2
                    stack.append(q)
        if not ok or len(sig) != n or len(set(sig.values())) != n:
            continue
        lift = []
        for v in range(G.V):
            p, w = G.word[v]
            u = G.read(sig[p], w)
            if u is None:
                ok = False
                break
            lift.append(u)
        if ok and len(set(lift)) == G.V:
            auts.append(lift)
    out.append(str(len(auts)))
    for a in auts:
        out.append(' '.join(map(str, a)))
    return '\n'.join(out)


def main():
    j = int(sys.argv[1])
    al = tuple(int(x) for x in sys.argv[2].split(','))
    be = tuple(int(x) for x in sys.argv[3].split(','))
    if len(sys.argv) > 4 and sys.argv[4] == 'cayley':
        PA, PB = cayley(al, be, 10 ** 6)
    else:
        PA, PB = list(al), list(be)
    print(instance_text(PA, PB, j))


if __name__ == '__main__':
    main()
