"""Malnormality test for a finitely generated B <= F(a,b) (Stallings).

B is malnormal iff every off-diagonal component of the pullback
core(B) x_R core(B) is a tree (Kapovich-Myasnikov).  Here core(B) is taken as
the fold of the base rose with B-generator loops (Q = one point), which may
carry hanging trees; those do not change which components have cycles.
Usage: python3 malnormal.py w1 w2 ...    (words as in chains.py)
"""
import sys
from chains import W
from foldlib import Graph, gamma


def core(words):
    G = Graph(gamma([0], [0], [W(s) for s in words]), 1, [0], [0])
    return G


def malnormal(words):
    G = core(words)
    V = G.V
    seen = set()
    for u in range(V):
        for v in range(V):
            if u == v or (u, v) in seen:
                continue
            comp = [(u, v)]
            seen.add((u, v))
            i = 0
            nE = 0
            while i < len(comp):
                x, y = comp[i]
                i += 1
                for k, x2 in G.nb[x].items():
                    y2 = G.nb[y].get(k)
                    if y2 is None:
                        continue
                    if k[1] == 1:
                        nE += 1
                    if (x2, y2) not in seen:
                        seen.add((x2, y2))
                        comp.append((x2, y2))
            diag = any(x == y for (x, y) in comp)
            if not diag and nE >= len(comp):
                return False, comp[:4]
    return True, None


def rank(words):
    G = core(words)
    E = sum(1 for v in range(G.V) for k in G.nb[v] if k[1] == 1)
    return E - G.V + 1


if __name__ == '__main__':
    ws = sys.argv[1:]
    print('rank', rank(ws), 'malnormal', malnormal(ws)[0])
