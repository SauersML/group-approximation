"""Distribution of law(K') = rk(K' : K'cap L_{j+1}) over all components of
size d, i.e. over all L_1-transitive L-sets P of size d up to isomorphism
(transport by phi^j).  Usage: python3 law_census.py d [maxlaw]
"""
import sys
from collections import Counter
from freefold import law0
from foldlib import depth_graphs
from multiorbit import comps
from bfs_free import classes


def main():
    d = int(sys.argv[1])
    maxlaw = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    hist = Counter()
    for PA, PB in classes(d):
        Gj, G, m = depth_graphs(PA, PB, 0)
        if len(set(comps(G))) != 1:
            hist['not L_1-transitive'] += 1
            continue
        hist[law0(PA, PB, maxlaw)] += 1
    print('d', d, dict(hist))


if __name__ == '__main__':
    main()
