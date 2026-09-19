"""Evaluate words in b, d at level k of the B-tree closed form (the model of levels_ck.py), recursively,
without any level table beyond the base.
A level-j element is (s, h_0..h_(M-1)) with s in Z/n and h_r level-(j-1) elements; level 0 is trivial.
From levels_ck.py: (s,h).b = (s, h_r . d^(3^r)),  (s,h).d = (s+1, h_(T r) . b)   (T = 3^-1 mod m, r mod M),
hence (s,h).b^j = (s, h_r . d^(j 3^r)) and (s,h).d^j = (s+j, h_(T^j r) . b^j).
A level-k element is stored as a list A[0..k-1], A[i] of shape (M,)*i holding the s-values at depth i.
usage: python3 evalk.py e k rels.txt [kept.txt]   -> prints, per relator, 1 if trivial at level k, else 0; summary
"""
import sys, re
import numpy as np
e, k = int(sys.argv[1]), int(sys.argv[2])
m = 2 ** e; n = m // 4; T = pow(3, -1, m); M = max(2 ** (e - 4), 2)
p3 = np.array([pow(3, r, n) for r in range(M)])
TP = np.array([[(pow(T, j, M) * r) % M for r in range(M)] for j in range(n)])   # TP[j][r] = T^j r mod M

def mul(A, gen, J):
    """right-multiply the element(s) A (list of arrays, A[i] shape S+(M,)*i) by gen^J, J of shape S"""
    if not A: return A
    S = A[0].shape
    if gen == 'b':
        if len(A) == 1: return A
        Jc = (J[..., None] * p3) % n          # exponent of d at child r
        return [A[0]] + mul_children(A[1:], S, 'd', Jc)
    Jn = J % n
    top = (A[0] + Jn) % n
    if len(A) == 1: return [top]
    perm = TP[Jn]                            # shape S+(M,): child q <- child perm[q]
    ch = [np.take_along_axis(a, perm.reshape(perm.shape + (1,) * (a.ndim - perm.ndim)), axis=len(S)) for a in A[1:]]
    return [top] + mul_children(ch, S, 'b', np.broadcast_to(Jn[..., None], S + (M,)))

def mul_children(C, S, gen, Jc):
    # C[i] has shape S+(M,)+(M,)*i ; each child is the level-(len(C)) element C[.][..., r, ...]
    return mul(C, gen, Jc) if C else C

def parse(wstr):
    out = []
    for t in wstr.strip().split('*'):
        mm = re.fullmatch(r'([bd])(?:\^(-?\d+))?', t)
        out.append((mm.group(1), int(mm.group(2) or 1)))
    return out

def trivial(word):
    A = [np.zeros((M,) * i, np.int64) for i in range(k)]
    for g, j in word:
        A = mul(A, g, np.array(j))
    return all((a == 0).all() for a in A)

if __name__ == '__main__':
    good = 0; tot = 0; bad = []
    keep = open(sys.argv[4], 'w') if len(sys.argv) > 4 else None
    for line in open(sys.argv[3]):
        if not line.strip(): continue
        t = trivial(parse(line)); tot += 1; good += t
        if not t: bad.append(tot)
        elif len(sys.argv) > 4: keep.write(line)
    print('e=%d level %d: %d of %d relators trivial; failures %s' % (e, k, good, tot, bad))
