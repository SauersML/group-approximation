"""Verify bounded-orbit (E) Cayley levels found by small_h.py.

For G = <alpha, beta> <= Sym(d) prints |G| and, for j = 1..J:
  tau_j = t_j(alpha, beta)  (as 'id', 'alpha' or 'other'),
  |H_j| = |<alpha, tau_j>|  (the common size of the L_j-orbits of the
          Cayley level), and whether (E) holds at depth j (Cayley
          criterion: the pi(u_c), c in V(C_j), lie in distinct right
          H_j-cosets).
Usage: python3 eb_verify.py J alpha beta      (comma lists)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from small_h import core_words, ev, gen, check  # noqa: E402

sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import t  # noqa: E402


def main():
    J = int(sys.argv[1])
    al = tuple(int(x) for x in sys.argv[2].split(','))
    be = tuple(int(x) for x in sys.argv[3].split(','))
    G = gen([al, be], 10 ** 6)
    print('alpha', al, 'beta', be, '|G|', len(G) if G else '>1e6')
    e = tuple(range(len(al)))
    for j in range(1, J + 1):
        words = core_words(j)
        tau = ev(t(j), al, be)
        name = 'id' if tau == e else ('alpha' if tau == al else 'other')
        r = check(al, be, j, words, t(j), 10 ** 6)
        print('j', j, '|C_j|', len(words), 'tau_j', name, '|H_j|', r[0], '(E)', r[1])
        sys.stdout.flush()


if __name__ == '__main__':
    main()
