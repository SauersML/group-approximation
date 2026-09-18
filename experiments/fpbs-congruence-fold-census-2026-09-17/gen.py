"""Finite L-sets Q for L = F(a, b), written as (n, A, B) with A[g] = a.g, B[g] = b.g.

Families:
  sl2 m     : the orbit of I in SL2(Z/m) under left multiplication by the Sanov
              matrices a = [[1,2],[0,1]], b = [[1,0],[2,1]] (m odd). Along m = p^k
              these are the levels of a free profinite action of F_2
              (F_2 embeds in SL2(Z) and the congruence kernels intersect trivially).
  sl2d m j  : as sl2, with generators (a, t_j), t_j = phi^j(b), phi(b) = b a b^-2.
  rand n s  : two uniform random permutations of n points (random Schreier graph).
  cyc N t   : Z/N with a = +1, b = +t (abelian odometer level; control).
  prod m N  : SL2(Z/m) x Z/N diagonally, a = (Sanov a, +1), b = (Sanov b, +1)
              (congruence level times an odometer with chi(a)=1, chi(b)=1).
Usage: python3 gen.py FAMILY ARGS... > file.bin
"""
import sys, struct, random
import numpy as np


def depth_generator(m, j):
    """t_j = phi^j(b) with phi(b) = b a b^-2, as a matrix mod m (Sanov a, b)."""
    def mul(x, y):
        return ((x[0]*y[0] + x[1]*y[2]) % m, (x[0]*y[1] + x[1]*y[3]) % m,
                (x[2]*y[0] + x[3]*y[2]) % m, (x[2]*y[1] + x[3]*y[3]) % m)

    def inv(x):
        return (x[3] % m, (-x[1]) % m, (-x[2]) % m, x[0] % m)
    a = (1, 2, 0, 1)
    t = (1, 0, 2, 1)
    for _ in range(j):
        ti = inv(t)
        t = mul(mul(t, a), mul(ti, ti))
    return a, t


def sl2_orbit(m, j=0):
    a, b = depth_generator(m, j)

    def mul(x, y):
        return ((x[0]*y[0] + x[1]*y[2]) % m, (x[0]*y[1] + x[1]*y[3]) % m,
                (x[2]*y[0] + x[3]*y[2]) % m, (x[2]*y[1] + x[3]*y[3]) % m)
    idx = {(1, 0, 0, 1): 0}
    elts = [(1, 0, 0, 1)]
    A, B = [], []
    i = 0
    while i < len(elts):
        g = elts[i]
        for s, arr in ((a, A), (b, B)):
            h = mul(s, g)
            j = idx.get(h)
            if j is None:
                j = len(elts); idx[h] = j; elts.append(h)
            arr.append(j)
        i += 1
    return len(elts), A, B


def main():
    fam = sys.argv[1]
    if fam == 'sl2':
        n, A, B = sl2_orbit(int(sys.argv[2]))
    elif fam == 'sl2d':
        # depth-j pair: generators (a, t_j) on the orbit of I; this is the
        # level-m quotient of the action a o phi^j of L (restricted to L_j)
        n, A, B = sl2_orbit(int(sys.argv[2]), int(sys.argv[3]))
    elif fam == 'rand':
        n = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
        A = list(range(n)); B = list(range(n)); rng.shuffle(A); rng.shuffle(B)
    elif fam == 'cyc':
        N, t = int(sys.argv[2]), int(sys.argv[3]); n = N
        A = [(q + 1) % N for q in range(N)]; B = [(q + t) % N for q in range(N)]
    elif fam == 'dih':
        # regular action of the dihedral group D_N = Z/N x| Z/2 (virtually abelian,
        # finite abelianization). mode 0: a = rotation, b = reflection;
        # mode 1: a = reflection, b = rotation; mode 2: a = s, b = s r.
        N, mode = int(sys.argv[2]), int(sys.argv[3]); n = 2 * N
        r, s = (1, 0), (0, 1)
        ga, gb = [(r, s), (s, r), (s, (1, 1))][mode]

        def dmul(x, y):
            return ((x[0] + (y[0] if x[1] == 0 else -y[0])) % N, (x[1] + y[1]) % 2)
        code = lambda x: x[0] * 2 + x[1]
        elts = [(k, e) for k in range(N) for e in range(2)]
        A = [0] * n; B = [0] * n
        for x in elts:
            A[code(x)] = code(dmul(ga, x)); B[code(x)] = code(dmul(gb, x))
    elif fam == 'prod':
        m, N = int(sys.argv[2]), int(sys.argv[3])
        n0, A0, B0 = sl2_orbit(m); n = n0 * N
        A = [A0[g] * N + (q + 1) % N for g in range(n0) for q in range(N)]
        B = [B0[g] * N + (q + 1) % N for g in range(n0) for q in range(N)]
    else:
        raise SystemExit('unknown family')
    out = sys.stdout.buffer
    out.write(struct.pack('<i', n))
    out.write(np.asarray(A, dtype='<i4').tobytes())
    out.write(np.asarray(B, dtype='<i4').tobytes())


if __name__ == '__main__':
    main()
