"""Test (RI_B) for B = L_1 = <a, b a b^-2> (rank 2, malnormal in F).

X = ker(B -> S3) (normal, index 6 in B, B/X = S3 needs 2 generators), so
rk(B : X) = d(S3) = 2.  Search g in F \\ B with <X, g> containing B.  Then
J = <X, g> has J cap B = B and rk((J cap B) : X) = 2 > 1 = rk(J : X): (RI_B)
fails for a rank-2 malnormal B.  The mod-p cokernel of H_1(X) -> H_1(B) is
H_1(S3; F_p): dim 1 for p = 2, 0 otherwise, so the homological test is blind.
"""
import itertools
import sys
from stall import fold_graph, member, rank, basis, red, L
from cover import kernel_graph

S3 = [p for p in itertools.permutations(range(3))]


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def generates_S3(p, q):
    seen = {tuple(range(3))}
    frontier = list(seen)
    while frontier:
        x = frontier.pop()
        for y in (p, q):
            z = compose(y, x)
            if z not in seen:
                seen.add(z)
                frontier.append(z)
    return len(seen) == 6


def regular(p):
    return tuple(S3.index(compose(p, x)) for x in S3)


def words(maxlen):
    frontier = ['']
    for _ in range(maxlen):
        new = []
        for w in frontier:
            for x in 'aAbB':
                if not w or red(w[-1] + x) != '':
                    new.append(w + x)
        for w in new:
            yield w
        frontier = new


def main(j=1, maxlen=7):
    Bg = L(j)
    GB = fold_graph(Bg)
    _, bgens, _ = basis(GB)
    print('B = L_%d gens' % j, Bg, 'Stallings basis', bgens)
    found = 0
    for p, q in itertools.product(S3, repeat=2):
        if not generates_S3(p, q):
            continue
        GX = kernel_graph(GB, [regular(p), regular(q)])
        _, xg, _ = basis(GX)
        assert rank(GX) == 7
        for g in words(maxlen):
            if member(GB, g):
                continue
            GJ = fold_graph(xg + [g])
            if all(member(GJ, w) for w in Bg):
                found += 1
                print('rho', p, q, 'g =', g, 'rk J =', rank(GJ),
                      '|core J| =', len(GJ[0]))
                break
    print('found', found)


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1,
         int(sys.argv[2]) if len(sys.argv) > 2 else 7)
