"""Pure single-edge hexagons in A_3 whose bottom triple has no upper bound at all.

B_4 on punctures q,a,b,t = strands 1..4; X = <s1,s2> (x-vertices: arcs from t to d0), Y = <s2,s3>
(y-vertices: arcs from a puncture to d1).  F = <A24, A34> (pushes of t around a, b), N = <A12, A13> (pushes of q
around a, b).  x1 = gamma0, x2 = a1.gamma0, x3 = a1 b1 a2.gamma0 with a_i in F, b1 in N.  (x1,x2) and (x2,x3) always
have the pure common neighbours y1 = delta0, y2 = a1 b1.delta0.  We ask:
  (i)  q lies in the d1-region of D - (x1 u x3)   [so a pure y3 exists and the 6-cycle closes], and
  (ii) no puncture lies in the d1-region of D - (x1 u x2 u x3)   [so NO vertex of any type bounds the triple].
Placement: pairwise crossing numbers are forced to equal curver's intersection numbers (arcs.tight).
Run: PYTHONPATH=.:<curver>:<realalg> python3 search2.py [L]"""
import sys, itertools
from arcs import xarc, tight
from search import cvarc

A24 = [3, 2, 2, -3]
A34 = [3, 3]
A12 = [1, 1]
A13 = [2, 1, 1, -2]


def inv(w):
    return [-g for g in reversed(w)]


def words(gens, L):
    """reduced words of length 1..L in the free group on gens (as braid words)"""
    letters = [(i, 1) for i in range(len(gens))] + [(i, -1) for i in range(len(gens))]
    out = []
    for n in range(1, L + 1):
        for w in itertools.product(letters, repeat=n):
            if any(w[k][0] == w[k + 1][0] and w[k][1] == -w[k + 1][1] for k in range(n - 1)):
                continue
            b = []
            for i, s in w:
                b += gens[i] if s == 1 else inv(gens[i])
            out.append((w, b))
    return out


def outer(braids):
    arcs = [xarc(b) for b in braids]
    target = {(i, j): cvarc(braids[i]).intersection(cvarc(braids[j]))
              for i in range(len(braids)) for j in range(i + 1, len(braids))}
    if any(v == 0 and arcs[i].word == arcs[j].word for (i, j), v in target.items()):
        return 'dup'
    P = tight(arcs, target)
    if P is None:
        return None
    r = P.regions([('P', 0), ('P', 1), ('P', 2), 'd1'])
    return frozenset(p for p in range(3) if r[p] == r[3])


def main(L=2, lo=0, hi=None):
    FA = words([A24, A34], L)
    NB = words([A12, A13], L)
    print('F words', len(FA), 'N words', len(NB))
    found = undet = tested = 0
    for (wa1, a1), (wb1, b1), (wa2, a2) in itertools.product(FA[lo:hi], NB, FA):
        x3 = a1 + b1 + a2
        s13 = outer([[], x3])
        if s13 is None:
            undet += 1
            continue
        if s13 == 'dup' or 0 not in s13:
            continue
        tested += 1
        s = outer([[], a1, x3])
        if s is None:
            undet += 1
            continue
        if s == 'dup':
            continue
        if len(s) == 0:
            found += 1
            print('CENTRELESS a1', wa1, 'b1', wb1, 'a2', wa2, 'x3word', xarc(x3).word, flush=True)
        elif len(s) == 1 and 0 not in s:
            print('  outer', sorted(s), 'a1', wa1, 'b1', wb1, 'a2', wa2, flush=True)
    print('closing 6-cycles tested', tested, 'centreless', found, 'undetermined', undet)


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    main(*a)
