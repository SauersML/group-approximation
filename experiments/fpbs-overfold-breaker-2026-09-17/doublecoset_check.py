"""Finite input (T_j) of the depth-shift lemma, as a SET equality.

H = L_{j+1}.  A type of the (a,b)-core C = C_{j+1} is an L-orbit on
off-diagonal pairs of H\\L meeting V(C)^2; it corresponds to the double coset
H g H, g = u_c u_{c'}^{-1} (u_c = base word of c).  Its level is >= 1 iff
g in L_1.  With T_H the minimal H-subtree of a Cayley tree, H g H is
realised in a core iff T_H meets g T_H (basis dependent!).

(T_j): { HgH realised in C, g in L_1 }  =  { HgH realised in C' },
where C' is the core of H in the basis (a, t_1) of L_1, i.e. C_j read with
b -> t_1.  Test for one g (tree projection):  write g in (a,t_1)-letters,
let p be its longest prefix readable in C' from the base, g = p s; then
T'_H meets g T'_H  iff  s^{-1} is readable in C' from the base.
Each level->=1 type of C is tested; the map type -> double coset is
injective, so if all pass and the counts agree the two sets are equal.
Usage: python3 doublecoset_check.py jmax
"""
import sys
from pb import core, iota

INV = {0: 1, 1: 0, 2: 3, 3: 2}      # KEYS index of inverse letter


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return out


def to_at1(g, C1):
    """(a,b)-word g in L_1 -> (a,t_1)-word, letters 0:a 1:a^-1 2:t 3:t^-1.
    Uses C_1 with spanning tree o-b-v1-b-v2: the a-loop at o is a, the a-edge
    v1->v2 is t_1."""
    nb = C1[0]
    o = 0
    v1 = nb[o][2]
    v2 = nb[v1][0]
    x = o
    out = []
    for letter in g:
        y = nb[x][letter]
        assert y >= 0, 'g not readable in C_1'
        if letter in (0, 1):
            if x == o and y == o:
                out.append(letter)            # a^{+-1}
            elif (x, y) == (v1, v2) and letter == 0:
                out.append(2)
            elif (x, y) == (v2, v1) and letter == 1:
                out.append(3)
            else:
                raise AssertionError('unexpected a-edge')
        x = y
    assert x == o, 'g not in L_1'
    return reduce(out)


def longest_prefix(w, nb):
    x = 0
    for k, letter in enumerate(w):
        y = nb[x][letter]
        if y < 0:
            return k
        x = y
    return len(w)


def readable(w, nb):
    return longest_prefix(w, nb) == len(w)


def main():
    jmax = int(sys.argv[1])
    C = [core(i) for i in range(jmax + 2)]
    C1 = C[1]
    from principal_types import components
    for j in range(1, jmax + 1):
        Cs = C[j + 1]
        nb, word = Cs
        # image in C_1 of each vertex
        img = list(range(len(nb)))
        for i in range(j, 0, -1):
            io = iota(C[i + 1], C[i])
            img = [io[x] for x in img]
        comps = components(nb)
        Cp = C[j][0]                       # C' = C_j with b read as t_1
        ge1 = ok = 0
        for comp in comps:
            c, d = comp[0]
            if img[c] != img[d]:
                continue                   # level 0
            ge1 += 1
            g = reduce(word[c] + [INV[x] for x in reversed(word[d])])
            w = to_at1(g, C1)
            k = longest_prefix(w, Cp)
            s = w[k:]
            sinv = [INV[x] for x in reversed(s)]
            ok += readable(sinv, Cp)
        ntypes_prev = len(components(Cp))
        print('j', j, 'level>=1 types of C_%d' % (j + 1), ge1,
              'realised in C\'', ok, '| types of C\' = C_%d' % j, ntypes_prev,
              'SET EQUAL' if ok == ge1 == ntypes_prev else 'FAIL')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
