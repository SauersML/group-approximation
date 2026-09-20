"""Explicit witnesses g (from one-pair hits) for a given X_0: prints g with
<phi X_0, g> = F and h with <X_0, h> = F, verified by direct folding.
usage: witness.py w1,w2,...
"""
import sys
from folding import *


def paths_from_base(n, edges):
    adj = {}
    for (u, l, v) in edges:
        adj.setdefault(u, []).append((l, v))
        adj.setdefault(v, []).append((l.upper(), u))
    word = {0: ''}
    q = [0]
    for v in q:
        for (l, t) in sorted(adj.get(v, [])):
            if t not in word:
                word[t] = word[v] + l
                q.append(t)
    return word


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def witness(words):
    n, E = graph_of(words)
    hits = one_pair_to_rose(n, E)
    if not hits:
        return None
    u, w = hits[0]
    P = paths_from_base(n, E)
    g = reduce_word(P[u] + inv(P[w]))
    assert is_rose(*graph_of(list(words) + [g])), 'witness failed'
    return g


if __name__ == '__main__':
    X0 = sys.argv[1].split(',')
    X = [phi(w) for w in X0]
    C1 = canon(*graph_of(['a', phi('b')]))
    print('X0 =', X0, ' phi X0 =', X)
    print('g with <phi X0, g> = F :', witness(X))
    print('h with <X0, h> = F     :', witness(X0))
    print('<X0,a>=F:', is_rose(*graph_of(X0 + ['a'])),
          ' <X0,b>=F:', is_rose(*graph_of(X0 + ['b'])))
    print('<phi X0, a> = L_1:', canon(*graph_of(X + ['a'])) == C1,
          ' <phi X0, t> = L_1:', canon(*graph_of(X + [phi('b')])) == C1)
