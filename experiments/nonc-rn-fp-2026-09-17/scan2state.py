"""All 2-state automata over a 2-letter alphabet: relators up to length L and those outside K_infinity."""
import sys, itertools
sys.path.insert(0, '.')
from autom import Automaton
from scan import scan
L = int(sys.argv[1]) if len(sys.argv) > 1 else 8
perms = [(0,1),(1,0)]
st = ['a','b','e']
seen=set()
for pa, pb in itertools.product(perms, perms):
    for sa in itertools.product(st, st):
        for sb in itertools.product(st, st):
            g = {'a': (pa, sa), 'b': (pb, sb)}
            A = Automaton(2, g)
            r, b, ex = scan(A, L, show=2)
            print(pa, sa, '|', pb, sb, ':', r, b, [(e[0], (A.fmt(e[1][0]), e[1][1]) if e[1] else None) for e in ex], flush=True)
