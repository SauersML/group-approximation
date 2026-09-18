#!/usr/bin/env python3
"""Exact check of the conjugation-pigeonhole certificate in P_{2,2}(J).

J = F_2<S,T | TS=1> (basis: monomials S^i T^j), Q = 1 + ST.
P = P_{2,2}(J) <= EL_4(J): n(Y) = [[1,Y],[0,1]], Levi diag(A,B), and
diag(A,B) n(Y) diag(A,B)^-1 = n(A Y B^-1).

Five elements (all words in elementary involutions x_ij(a), char 2):
    u  = x_13(1)                                  = n(E_11)
    g  = x_12(S) x_21(T) x_12(S) x_12(1) x_21(1) x_12(1)
       = diag(u2, 1),  u2 = [[S,Q],[0,T]]         (left Levi)
    e  = x_12(1)                                  (left Levi)
    r1 = x_34(1)                                  (right Levi)
    r2 = x_43(S) x_34(1)                          (right Levi)
Relations checked exactly (they hold in P, hence in P_{2,2}(R) for every
ring R with ts = 1, via J -> R):
    (P1) [g, r1] = [g, r2] = 1
    (P2) g u g^-1 = (r2 u r2^-1)(r1 u r1^-1)^-1
    (P3) [e, u] = [e, r1] = [e, r2] = 1
and the identity
    (H)  e (g^-1 u g) e^-1 (g^-1 u g)^-1 = x_13(Q)   (the head), != 1.
Pigeonhole: in a finite group, A = <R-conjugates of u> (R = <r1,r2>) is
finite, g A g^-1 <= A by (P1),(P2), so g A g^-1 = A and g^-1 u g lies in A;
e centralizes A by (P3); so the left side of (H) is 1 and the head dies.
Exit status 0 iff every check passes.
"""
import sys


def jmul_mono(a, b):
    i, j = a
    k, l = b
    if j <= k:
        return (i + k - j, l)
    return (i, j - k + l)


def jadd(x, y):
    return frozenset(set(x) ^ set(y))


def jmul(x, y):
    out = set()
    for a in x:
        for b in y:
            out ^= {jmul_mono(a, b)}
    return frozenset(out)


ZERO = frozenset()
ONE = frozenset({(0, 0)})
S = frozenset({(1, 0)})
T = frozenset({(0, 1)})
Q = frozenset({(0, 0), (1, 1)})
N4 = 4


def mat_id():
    return tuple(tuple(ONE if r == c else ZERO for c in range(N4)) for r in range(N4))


def mat_mul(A, B):
    return tuple(tuple(
        _dot(A, B, r, c) for c in range(N4)) for r in range(N4))


def _dot(A, B, r, c):
    acc = ZERO
    for k in range(N4):
        acc = jadd(acc, jmul(A[r][k], B[k][c]))
    return acc


def elem(i, j, a):
    M = [list(r) for r in mat_id()]
    M[i - 1][j - 1] = jadd(M[i - 1][j - 1], a)
    return tuple(tuple(r) for r in M)


# a group element is a word: list of (i, j, a) elementary involutions
def val(word):
    M = mat_id()
    for (i, j, a) in word:
        M = mat_mul(M, elem(i, j, a))
    return M


def inv(word):
    return list(reversed(word))  # each letter is an involution (char 2)


def cat(*ws):
    out = []
    for w in ws:
        out += w
    return out


u = [(1, 3, ONE)]
g = [(1, 2, S), (2, 1, T), (1, 2, S), (1, 2, ONE), (2, 1, ONE), (1, 2, ONE)]
e = [(1, 2, ONE)]
r1 = [(3, 4, ONE)]
r2 = [(4, 3, S), (3, 4, ONE)]


def conj(x, y):
    return cat(x, y, inv(x))


def comm(x, y):
    return cat(x, y, inv(x), inv(y))


def main():
    ok = True
    I = mat_id()

    def check(name, cond):
        nonlocal ok
        print("%-58s %s" % (name, "ok" if cond else "FAIL"))
        ok = ok and cond

    G = val(g)
    u2 = ((S, Q), (ZERO, T))
    check("g = diag(u2,1), u2 = [[S,Q],[0,T]]",
          all(G[r][c] == (u2[r][c] if r < 2 and c < 2 else (ONE if r == c else ZERO))
              for r in range(4) for c in range(4)))
    check("(P1) [g,r1] = 1", val(comm(g, r1)) == I)
    check("(P1) [g,r2] = 1", val(comm(g, r2)) == I)
    lhs = val(conj(g, u))
    rhs = val(cat(conj(r2, u), inv(conj(r1, u))))
    check("(P2) g u g^-1 = x_13(S)", lhs == elem(1, 3, S))
    check("(P2) g u g^-1 = (r2 u r2^-1)(r1 u r1^-1)^-1", lhs == rhs)
    check("(P3) [e,u] = 1", val(comm(e, u)) == I)
    check("(P3) [e,r1] = 1", val(comm(e, r1)) == I)
    check("(P3) [e,r2] = 1", val(comm(e, r2)) == I)
    x = conj(inv(g), u)  # g^-1 u g
    X = val(x)
    check("g^-1 u g = x_13(T) x_23(Q)", X == mat_mul(elem(1, 3, T), elem(2, 3, Q)))
    H = val(comm(e, x))
    check("(H) [e, g^-1 u g] = x_13(Q)", H == elem(1, 3, Q))
    check("head x_13(Q) != 1", elem(1, 3, Q) != I)
    # control: without (P2) the pigeonhole has nothing to act on; g^-1 u g
    # is not a product of R-conjugates of u in P (its x_23 entry is Q != 0,
    # while every R-conjugate n(E_11 B^-1) has zero second row).
    check("control: x_23-entry of g^-1 u g is Q (row 2 nonzero)", X[1][2] == Q)
    print("ALL CHECKS PASS" if ok else "SOME CHECK FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
