"""Group eigenvalue-1 elements of rho_k(F) by their fixed vector.

Input: census output lines "HIT k=K EIG1-other len=n WORD" (and UNI/TOR/NEG lines).
For each word compute the exact integer matrix M, the primitive integer kernel vector v
of M - I (when the eigenvalue 1 is simple) and group words by +-v.
Elements fixing the same v lie in Stab(v) = Z^2 x| SL_2(Z); an element of the subgroup
they generate that acts trivially on Z^3/Zv is a transvection with direction v.
Prints the most populated fixed vectors.
"""
import sys
from math import gcd
from collections import defaultdict

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from verify import word, I3, sub


def cross(a, b): return [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]


def prim(v):
    g = 0
    for c in v:
        g = gcd(g, abs(c))
    if g == 0:
        return None
    v = [c // g for c in v]
    for c in v:
        if c != 0:
            if c < 0:
                v = [-d for d in v]
            break
    return tuple(v)


def kernel_vec(A):
    # A = M - I has rank 2 generically: kernel spanned by cross product of two independent rows
    rows = A
    for i in range(3):
        for j in range(i + 1, 3):
            c = cross(rows[i], rows[j])
            if any(c):
                return prim(c)
    return None


def main(path, k, top=15):
    groups = defaultdict(list)
    lgroups = defaultdict(list)
    n = 0
    for line in open(path):
        if not line.startswith('HIT') or 'EIG1' not in line:
            continue
        w = line.split()[-1]
        M = word(k, w)
        A = sub(M, I3)
        v = kernel_vec(A)
        # left fixed vector: kernel of A^T
        At = [[A[j][i] for j in range(3)] for i in range(3)]
        u = kernel_vec(At)
        if v is None:
            continue
        groups[v].append(w)
        lgroups[u].append(w)
        n += 1
    print('k=%d: %d eigenvalue-1 words, %d distinct fixed vectors, %d distinct fixed covectors' % (k, n, len(groups), len(lgroups)))
    for v, ws in sorted(groups.items(), key=lambda t: -len(t[1]))[:top]:
        print('  v=%s: %d words, e.g. %s' % (v, len(ws), ' '.join(sorted(ws, key=len)[:6])))
    for u, ws in sorted(lgroups.items(), key=lambda t: -len(t[1]))[:5]:
        print('  covector u=%s: %d words, e.g. %s' % (u, len(ws), ' '.join(sorted(ws, key=len)[:6])))


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]))
