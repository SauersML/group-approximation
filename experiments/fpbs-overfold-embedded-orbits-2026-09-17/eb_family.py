"""Candidate (E-B) family: G = Sym(d), beta a d-cycle, alpha a transposition
of two cyclically adjacent points.

For d = d0..d1 and each choice of adjacent transposition (0 1) or (d-1 0)
with beta : i -> i+1 mod d (right action x.beta = beta[x]), print, for
j = 1..min(d-1, J), |H_j| = |<alpha, tau_j>|, tau_j in {id, alpha, other},
and (E) at depth j (Cayley criterion, see small_h.check).
Usage: python3 eb_family.py d0 d1 J
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from small_h import core_words, ev, check  # noqa: E402

sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import t  # noqa: E402


def main():
    d0, d1, J = [int(x) for x in sys.argv[1:4]]
    words = {}
    for d in range(d0, d1 + 1):
        be = tuple((i + 1) % d for i in range(d))
        for name, (x, y) in (('(0 1)', (0, 1)), ('(d-1 0)', (d - 1, 0))):
            al = list(range(d))
            al[x], al[y] = y, x
            al = tuple(al)
            e = tuple(range(d))
            row = []
            for j in range(1, min(d - 1, J) + 1):
                if j not in words:
                    words[j] = core_words(j)
                tau = ev(t(j), al, be)
                tn = 'id' if tau == e else ('al' if tau == al else '*')
                r = check(al, be, j, words[j], t(j), 10 ** 7)
                row.append('j%d:|H|=%d,%s,%s' % (j, r[0], tn, 'E' if r[1] else '-'))
            print('d', d, 'alpha', name, ' '.join(row))
            sys.stdout.flush()


if __name__ == '__main__':
    main()
