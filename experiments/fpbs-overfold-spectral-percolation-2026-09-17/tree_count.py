"""Exact F(B_r x types) in the Cayley tree of F(a,b) (the free action).

Points are reduced words; x.g is right multiplication.  A hyperedge (q, k)
has atoms (q g_{k,p}, i_{k,p}) with g the inverse-words of hyper.build.
F(B_r x types) = #{(q,k): all three q g_{k,p} have length <= r}.
Usage: python3 tree_count.py j rmax
"""
import sys
from hyper import build

INV = [1, 0, 3, 2]


def mul(x, w):
    x = list(x)
    for k in w:
        if x and x[-1] == INV[k]:
            x.pop()
        else:
            x.append(k)
    return tuple(x)


def words(r):
    out = [()]
    fr = [()]
    for _ in range(r):
        nf = []
        for x in fr:
            for k in range(4):
                if x and x[-1] == INV[k]:
                    continue
                nf.append(x + (k,))
        out += nf
        fr = nf
    return out


def main():
    j, rmax = int(sys.argv[1]), int(sys.argv[2])
    M = build(j)
    R = M['R']
    L = max(len(w) for ent in M['hyp'] for _, w in ent)
    law = M['lawful'].index(True)
    for r in range(1, rmax + 1):
        pts = words(r + L)
        F = FL = 0
        for q in pts:
            for ent in M['hyp']:
                if all(len(mul(q, w)) <= r for _, w in ent):
                    F += 1
                    if all(i == law for i, _ in ent):
                        FL += 1
        size = len(words(r))
        print('j %d r %d |B_r| %d  F(B_r x types) %d  |A| %d  ratio %.4f'
              '  lawful F_LLL/|B_r| %.4f'
              % (j, r, size, F, size * R, F / (size * R), FL / size))


if __name__ == '__main__':
    main()
