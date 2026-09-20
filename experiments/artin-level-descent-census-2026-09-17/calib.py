"""Calibration of census.py on the decided 2x2 dead joins
(artin-2x2-dead-joins-sigma1-iff-k-q-odd-family): members are exactly halves with three 2s
and one odd entry."""
import random

from census import analyse


def join(h):  # halves (ac, bc, be, ae)
    V = ['a', 'b', 'c', 'e']
    E = {('a', 'b'): 2, ('c', 'e'): 2, ('a', 'c'): 2 * h[0], ('b', 'c'): 2 * h[1],
         ('b', 'e'): 2 * h[2], ('a', 'e'): 2 * h[3]}
    chi = {'a': 1, 'b': 1, 'c': -1, 'e': -1}
    return V, E, chi


if __name__ == "__main__":
    rng = random.Random(1)
    for h in [(2, 2, 2, 3), (2, 2, 2, 5), (2, 2, 2, 2), (2, 3, 2, 5), (2, 3, 2, 4),
              (3, 3, 3, 3), (2, 2, 3, 3), (2, 2, 2, 4)]:
        V, E, chi = join(h)
        res, b, c = analyse(V, E, chi, rng, nreps=80)
        print(h, res, flush=True)
