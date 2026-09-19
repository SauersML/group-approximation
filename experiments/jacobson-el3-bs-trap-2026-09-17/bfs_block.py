# BFS in the (1,3) block EL_2(J), J = F_2<S,T | TS=1>.
# A J element is a frozenset of monomials (a,b) meaning S^a T^b (F_2 coefficients).
# Searches words in x(1), x(S), y(1), y(T) for x(S^2) and y(T^2).
import sys


def mono_mul(m, n):
    a, b = m
    c, d = n
    if b >= c:
        return (a, b - c + d)
    return (a + c - b, d)


def jmul(x, y):
    r = set()
    for m in x:
        for n in y:
            r ^= {mono_mul(m, n)}
    return frozenset(r)


def jadd(x, y):
    return frozenset(set(x) ^ set(y))


Z = frozenset()
O = frozenset({(0, 0)})


def mmul(A, B):
    return (jadd(jmul(A[0], B[0]), jmul(A[1], B[2])), jadd(jmul(A[0], B[1]), jmul(A[1], B[3])),
            jadd(jmul(A[2], B[0]), jmul(A[3], B[2])), jadd(jmul(A[2], B[1]), jmul(A[3], B[3])))


def x(r):
    return (O, r, Z, O)


def y(r):
    return (O, Z, r, O)


S = frozenset({(1, 0)})
T = frozenset({(0, 1)})


def main():
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
    gens = {'X1': x(O), 'XS': x(S), 'Y1': y(O), 'YT': y(T)}
    I = (O, Z, Z, O)
    targets = {'x(S^2)': x(frozenset({(2, 0)})), 'y(T^2)': y(frozenset({(0, 2)}))}
    seen = {I: ''}
    frontier = [I]
    for L in range(1, 60):
        nf = []
        for g in frontier:
            w = seen[g]
            last = w.split(' ')[-1] if w else ''
            for nm, h in gens.items():
                if nm == last:
                    continue
                k = mmul(g, h)
                if k not in seen:
                    seen[k] = (w + ' ' + nm) if w else nm
                    nf.append(k)
                    for tn, tv in targets.items():
                        if k == tv:
                            print('FOUND', tn, 'length', L, ':', seen[k], flush=True)
        frontier = nf
        print('len', L, 'new', len(nf), 'total', len(seen), flush=True)
        if len(seen) > maxn or not nf:
            break


if __name__ == '__main__':
    main()
