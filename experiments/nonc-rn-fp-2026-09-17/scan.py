"""Scan reduced words up to length L: count relators (trivial in G) and those not in K_infinity."""
import sys, itertools
sys.path.insert(0, '.')
from autom import Automaton

def reduced_words(k, L):
    letters = [i for i in range(1, k + 1)] + [-i for i in range(1, k + 1)]
    def rec(w):
        yield w
        if len(w) == L:
            return
        for u in letters:
            if w and w[-1] == -u:
                continue
            yield from rec(w + (u,))
    yield from rec(())

def scan(A, L, show=5):
    k = len(A.names)
    rel = bad = 0
    ex = []
    for w in reduced_words(k, L):
        if not w:
            continue
        if A.is_trivial(w):
            rel += 1
            if not A.in_K_inf(w):
                bad += 1
                if len(ex) < show:
                    ex.append((A.fmt(w), A.cycle_witness(w)))
    return rel, bad, ex

AUT = {
 'lamplighter': (2, {'a': ((1,0), ('a','b')), 'b': ((0,1), ('a','b'))}),
 'odometer+linear b=(a,b)': (2, {'a': ((1,0), ('e','a')), 'b': ((0,1), ('a','b'))}),
 'odometer+linear b=(b,a)': (2, {'a': ((1,0), ('e','a')), 'b': ((0,1), ('b','a'))}),
 'odometer+linear b=sigma(a,b)': (2, {'a': ((1,0), ('e','a')), 'b': ((1,0), ('a','b'))}),
 'odometer+linear b=sigma(b,a)': (2, {'a': ((1,0), ('e','a')), 'b': ((1,0), ('b','a'))}),
 'odometer+linear b=(b,a^-1)?': (2, {'a': ((1,0), ('e','a')), 'b': ((0,1), ('b','b'))}),
}
if __name__ == '__main__':
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for name, (d, g) in AUT.items():
        A = Automaton(d, g)
        r, b, ex = scan(A, L)
        print(f'{name}: relators<= {L}: {r}, not in K_inf: {b}')
        for e in ex:
            print('   ', e[0], '| cycle:', (A.fmt(e[1][0]), e[1][1]) if e[1] else None)
