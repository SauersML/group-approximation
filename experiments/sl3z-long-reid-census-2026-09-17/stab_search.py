"""Transvection search through fixed-vector stabilizers.

For each fixed vector v shared by several eigenvalue-1 words g_i of rho_k(F), compute the
action A_i of g_i on Q^3/Qv (2x2 rational matrices). An element of <g_i> that fixes v and
acts trivially on Q^3/Qv is I + v w^T with w.v = 0, i.e. a transvection (or I).
We search words of length <= R in the g_i (and inverses) whose quotient image is I but
whose upstairs matrix is not I. Hits are rank-one unipotents in rho_k(F).
"""
import sys
import itertools
from fractions import Fraction
from collections import defaultdict

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from verify import word, I3, sub, mul, adj
from eig1_groups import kernel_vec


def inv3(M): return adj(M)


def quotient_action(M, v):
    # basis B = [v, e_a, e_b] with det != 0; B^-1 M B = [[1, *], [0, A]]
    for a, b in ((0, 1), (0, 2), (1, 2)):
        B = [[Fraction(v[i]), Fraction(1 if i == a else 0), Fraction(1 if i == b else 0)] for i in range(3)]
        det = (B[0][0] * (B[1][1] * B[2][2] - B[1][2] * B[2][1]) - B[0][1] * (B[1][0] * B[2][2] - B[1][2] * B[2][0])
               + B[0][2] * (B[1][0] * B[2][1] - B[1][1] * B[2][0]))
        if det != 0:
            break
    Binv = [[x / det for x in row] for row in adj(B)]
    C = mul(mul(Binv, M), B)
    return ((C[1][1], C[1][2]), (C[2][1], C[2][2]))


def m2(A, B): return ((A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]),
                      (A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]))


def i2(A):
    d = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    return ((A[1][1] / d, -A[0][1] / d), (-A[1][0] / d, A[0][0] / d))


ID2 = ((1, 0), (0, 1))


def search(k, path, R=4, maxgen=8, mingroup=2):
    groups = defaultdict(list)
    for line in open(path):
        if line.startswith('HIT') and 'EIG1' in line:
            w = line.split()[-1]
            M = word(k, w)
            v = kernel_vec(sub(M, I3))
            if v is not None:
                groups[v].append(w)
    hits = 0
    tested = 0
    for v, ws in sorted(groups.items(), key=lambda t: -len(t[1])):
        if len(ws) < mingroup:
            break
        ws = sorted(ws, key=len)[:maxgen]
        gens = []
        for w in ws:
            M = word(k, w)
            Mi = inv3(M)
            A = quotient_action(M, v)
            gens.append((w, M, A))
            gens.append((w[::-1].swapcase(), Mi, i2(A)))
        tested += 1
        # BFS over words in gens up to length R, keyed by quotient matrix
        seen = {ID2: ('', I3)}
        frontier = [('', I3, ID2, -1)]
        found = False
        for r in range(R):
            nf = []
            for (s, M, A, last) in frontier:
                for gi, (gw, GM, GA) in enumerate(gens):
                    if last >= 0 and gi == last ^ 1:
                        continue
                    A2 = m2(A, GA)
                    M2 = mul(M, GM)
                    s2 = s + '.' + gw
                    if A2 in seen:
                        s0, M0 = seen[A2]
                        D = mul(inv3(M0), M2)
                        if D != I3:
                            N = sub(D, I3)
                            print('k=%d v=%s: quotient collision %s vs %s => element acting trivially on Q^3/Qv, D-I=%s'
                                  % (k, v, s0, s2, N))
                            hits += 1
                            found = True
                            break
                    else:
                        seen[A2] = (s2, M2)
                        nf.append((s2, M2, A2, gi))
                if found:
                    break
            if found:
                break
            frontier = nf
    print('k=%d: tested %d fixed vectors with >= %d words, hits %d' % (k, tested, mingroup, hits))


if __name__ == '__main__':
    search(int(sys.argv[2]), sys.argv[1], R=int(sys.argv[3]) if len(sys.argv) > 3 else 3)
