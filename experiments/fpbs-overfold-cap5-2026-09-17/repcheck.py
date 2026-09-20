"""Check that an instance file's lawful seed list has one representative for
EVERY nontrivial single-lawful-seed closure class (not merely per orbit), so
that lcheck's unreduced ell search over these representatives is exact.

Usage: python3 repcheck.py inst.txt
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ostep_verify import load, closure  # noqa: E402


def can(lab):
    f = {}
    return tuple(f.setdefault(c, len(f)) for c in lab)


def main():
    path = sys.argv[1]
    tok = open(path).read().split()
    V, nb, m = load(path)
    p = 2 + 4 * V + V
    over = [int(x) for x in tok[p:p + V]]
    p += V
    S = int(tok[p])
    p += 1
    seeds = [tuple(int(x) for x in tok[p + 3 * i:p + 3 * i + 3]) for i in range(S)]
    base = can(closure(V, nb, []))
    print('V', V, 'base classes', len(set(base)))
    cls = {}
    for u, v in itertools.combinations(range(V), 2):
        if m[u] == m[v]:
            c = can(closure(V, nb, [(u, v)]))
            if c != base:
                cls.setdefault(c, (u, v))
    print('distinct nontrivial lawful single-seed closures', len(cls))
    inst = set(can(closure(V, nb, [(u, v)])) for u, v, lw in seeds if lw)
    print('instance lawful reps', sum(s[2] for s in seeds),
          'distinct closures among them', len(inst),
          'covering', len(inst & set(cls)), 'of', len(cls))
    same = all(over[u] == over[v] for u, v in itertools.combinations(range(V), 2)
               if m[u] == m[v])
    print('lawful pairs lie in one over-fibre:', same)


if __name__ == '__main__':
    main()
