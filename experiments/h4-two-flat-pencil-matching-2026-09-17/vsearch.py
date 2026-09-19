"""Genuine Case 1 tuples WITHOUT a hexagon-vertex pure centre (the only ones a joint-shadow certificate can refute).

(*)  beta_3^-1 (alpha_1 alpha_2) beta_3 = alpha_1 beta_1 alpha_2 beta_1^-1,  alpha_i in F \ 1, alpha_1 alpha_2 != 1,
beta_i in N, beta_1 beta_3 != 1.  Stage 1 hashes both sides of (*) by their Burau matrices (7 strands, t = T mod
the prime Q) in the three I_2(5) shadows; stage 2 confirms a hit exactly in the Artin action on F_7 in all three
shadows (fg.py) and then in the H_4 Artin group (Garside); stage 3 asks whether one of the conjugates
c_01 = beta_1 alpha_2 beta_1^-1, c_12 = beta_1^-1 alpha_1 beta_1, c_20 = beta_3 alpha_1 beta_3^-1 lies in F (then u_P
is a genuine pure centre; the first such P is reported; test as in purecent.py with F-words of length <= LF).
alpha over F-words of length <= LA, beta over words of length <= LB in the 9 N-letters acting non-trivially in
some shadow.  Prints NOVERTEX lines for genuine tuples with no hexagon-vertex centre.
Run: python3 vsearch.py LA LB [LF [K r]]   (chunk: alpha_1 index = r mod K)"""
import sys, time
import numpy as np
from collections import Counter
from zsearch3 import FN, EFF3, act3, inv, c3
from fg import words, spec, aut, FGEN, NGEN
from ejection import elt, genuine
from joint import nf, inv as linv

Q, T = 268435399, 91138233
TI = pow(T, Q - 2, Q)
BY = {g[0]: g for g in FGEN + NGEN}


def smat(i, e):
    M = np.eye(7, dtype=np.int64)
    if e == 1:
        M[i - 1, i - 1], M[i - 1, i], M[i, i - 1], M[i, i] = (1 - T) % Q, T, 1, 0
    else:
        M[i - 1, i - 1], M[i - 1, i], M[i, i - 1], M[i, i] = 0, 1, TI, (1 - TI) % Q
    return M


SM = {(i, e): smat(i, e) for i in range(1, 7) for e in (1, -1)}


def bur(braid):
    M = np.eye(7, dtype=np.int64)
    for g in braid:
        M = (M @ SM[(abs(g), 1 if g > 0 else -1)]) % Q
    return M


def bur3(w):
    """Burau matrices of the three shadow images of a word [(name, sign)]"""
    out = []
    for a in range(3):
        br = []
        for n, s in w:
            im = BY[n][2][a]
            br += im if s == 1 else [-x for x in reversed(im)]
        out.append(bur(br))
    return out


def mm(*Ms):
    R = Ms[0]
    for M in Ms[1:]:
        R = [(R[a] @ M[a]) % Q for a in range(3)]
    return R


def key(M):
    return b''.join(m.tobytes() for m in M)


def main(LA, LB, LF=5, K=1, r=0):
    SA = words(FN, LA)
    B = [()] + words(EFF3, LB)
    BM = [(w, bur3(w), bur3(inv(w))) for w in B]
    FM = {a: bur3(a) for a in SA}
    table = {}
    for w in [()] + words(FN, LF):
        e = elt(spec(w))
        table.setdefault(aut(e[2][0]), e)
    st = Counter(); t = time.time()
    print('alphas', len(SA), 'betas', len(B), flush=True)
    for i1, a1 in enumerate(SA):
        if i1 % K != r:
            continue
        for a2 in SA:
            if a1 + a2 and red_is_one(a1 + a2):
                continue
            A1, A2 = FM[a1], FM[a2]
            A12 = mm(A1, A2)
            lhs = {}
            for w3, b3, b3i in BM:
                lhs.setdefault(key(mm(b3i, A12, b3)), []).append(w3)
            for w1, b1, b1i in BM:
                for w3 in lhs.get(key(mm(A1, b1, A2, b1i)), []):
                    if w1 == inv(w3):
                        continue
                    st['burau hits'] += 1
                    if c3(act3(inv(w3)), c3(act3(a1 + a2), act3(w3))) != c3(act3(a1), c3(act3(w1), c3(act3(a2), act3(inv(w1))))):
                        st['burau false positive'] += 1; continue
                    E = [elt(spec(x)) for x in (a1, w1, a2, w3)]
                    if not genuine(*E):
                        st['shadow only'] += 1; continue
                    st['genuine'] += 1
                    ea1, eb1, ea2, eb3 = E
                    C = {'01': (eb1[1] + ea2[1] + linv(eb1[1]), eb1[2][0] + ea2[2][0] + linv(eb1[2][0])),
                         '12': (linv(eb1[1]) + ea1[1] + eb1[1], linv(eb1[2][0]) + ea1[2][0] + eb1[2][0]),
                         '20': (eb3[1] + ea1[1] + linv(eb3[1]), eb3[2][0] + ea1[2][0] + linv(eb3[2][0]))}
                    pure = next(([P] for P, (h, im) in C.items()
                                 if (f := table.get(aut(im))) is not None and nf(h) == nf(f[1])), [])
                    st[('vertex centres',) + tuple(pure)] += 1
                    if not pure:
                        print('NOVERTEX', spec(a1), '|', spec(w1), '|', spec(a2), '|', spec(w3), flush=True)
        st['pairs done'] += 1
    print(dict(st), round(time.time() - t), 's', flush=True)


def red_is_one(w):
    out = []
    for g in w:
        if out and out[-1][0] == g[0] and out[-1][1] == -g[1]:
            out.pop()
        else:
            out.append(g)
    return not out


if __name__ == '__main__':
    A = [int(x) for x in sys.argv[1:]]
    main(*A)
