#!/usr/bin/env python3
"""Integral (signed) version of the conjugation-pigeonhole certificate.

J_Z = Z<S,T | TS=1>, Z-basis S^i T^j, Q = 1 - ST (idempotent, QS = 0, TQ = 0).
Any ring R with elements t s = 1 receives J_Z -> R, S -> s, T -> t; the
image of Q is 1 - st, nonzero exactly when R is not directly finite at (s,t).
So every relation checked here holds in P_{2,2}(R) = M_2(R) x| (EL_2(R)^2)
for every such R, with the head x_13(1-st) != 1.

Elements (x_ij(a) = 1 + a e_ij, inverse x_ij(-a)):
    u  = x_13(1)
    g  = x_12(S) x_21(-T) x_12(S) x_21(1) x_12(-1) x_21(1)   (w K, K = [[0,-1],[1,0]])
       = diag(u2, 1), u2 = [[S,-Q],[0,T]],  u2^-1 = [[T,0],[-Q,S]]
    e  = x_12(1)
    r1 = x_34(-1)
    r2 = x_43(-S) x_34(-1)
Checks: (P1) [g,r1]=[g,r2]=1; (P2) g u g^-1 = x_13(S) = (r2 u r2^-1)(r1 u r1^-1)^-1;
(P3) [e,u]=[e,r1]=[e,r2]=1; g^-1 u g = x_13(T) x_23(-Q);
(H) [e, g^-1 u g] = x_13(-Q) != 1.   Exit 0 iff all pass.
"""
import sys


def mono(a, b):
    (i, j), (k, l) = a, b
    return (i + k - j, l) if j <= k else (i, j - k + l)


def add(x, y, c=1):
    out = dict(x)
    for m, v in y.items():
        out[m] = out.get(m, 0) + c * v
        if out[m] == 0:
            del out[m]
    return out


def mul(x, y):
    out = {}
    for a, u in x.items():
        for b, v in y.items():
            m = mono(a, b)
            out[m] = out.get(m, 0) + u * v
            if out[m] == 0:
                del out[m]
    return out


def neg(x):
    return {m: -v for m, v in x.items()}


def key(x):
    return tuple(sorted(x.items()))


ZERO, ONE = {}, {(0, 0): 1}
S, T = {(1, 0): 1}, {(0, 1): 1}
Q = {(0, 0): 1, (1, 1): -1}
N = 4


def mid():
    return [[dict(ONE) if r == c else {} for c in range(N)] for r in range(N)]


def mmul(A, B):
    C = [[{} for _ in range(N)] for _ in range(N)]
    for r in range(N):
        for c in range(N):
            acc = {}
            for k in range(N):
                acc = add(acc, mul(A[r][k], B[k][c]))
            C[r][c] = acc
    return C


def meq(A, B):
    return all(key(A[r][c]) == key(B[r][c]) for r in range(N) for c in range(N))


def x(i, j, a):
    M = mid()
    M[i - 1][j - 1] = add(M[i - 1][j - 1], a)
    return M


def val(word):
    M = mid()
    for (i, j, a) in word:
        M = mmul(M, x(i, j, a))
    return M


def inv(word):
    return [(i, j, neg(a)) for (i, j, a) in reversed(word)]


def conj(p, q):
    return p + q + inv(p)


def comm(p, q):
    return p + q + inv(p) + inv(q)


u = [(1, 3, ONE)]
g = [(1, 2, S), (2, 1, neg(T)), (1, 2, S), (2, 1, ONE), (1, 2, neg(ONE)), (2, 1, ONE)]
e = [(1, 2, ONE)]
r1 = [(3, 4, neg(ONE))]
r2 = [(4, 3, neg(S)), (3, 4, neg(ONE))]


def main():
    ok = True
    I = mid()

    def check(name, cond):
        nonlocal ok
        print("%-58s %s" % (name, "ok" if cond else "FAIL"))
        ok = ok and cond

    G = val(g)
    target = mid()
    target[0][0], target[0][1], target[1][0], target[1][1] = S, neg(Q), {}, T
    check("g = diag(u2,1), u2 = [[S,-Q],[0,T]]", meq(G, target))
    check("(P1) [g,r1] = 1", meq(val(comm(g, r1)), I))
    check("(P1) [g,r2] = 1", meq(val(comm(g, r2)), I))
    lhs = val(conj(g, u))
    check("(P2) g u g^-1 = x_13(S)", meq(lhs, x(1, 3, S)))
    check("(P2) = (r2 u r2^-1)(r1 u r1^-1)^-1",
          meq(lhs, val(conj(r2, u) + inv(conj(r1, u)))))
    check("(P3) [e,u] = 1", meq(val(comm(e, u)), I))
    check("(P3) [e,r1] = 1", meq(val(comm(e, r1)), I))
    check("(P3) [e,r2] = 1", meq(val(comm(e, r2)), I))
    X = val(conj(inv(g), u))
    check("g^-1 u g = x_13(T) x_23(-Q)", meq(X, mmul(x(1, 3, T), x(2, 3, neg(Q)))))
    check("(H) [e, g^-1 u g] = x_13(-Q)", meq(val(comm(e, conj(inv(g), u))), x(1, 3, neg(Q))))
    check("head x_13(-Q) != 1 (Q != 0 in J_Z)", not meq(x(1, 3, neg(Q)), I))
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
