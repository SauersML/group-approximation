"""Exact membership g in F for pure elements g of the H_4 Artin group (letters +-1..4 = s_1..s_4).

F = ker(P_Y -> P_Z) = <p1, p2, p3>, Y = {s1,s2,s3} (type A_3 = B_4, s_i = sigma_i), Z = {s2,s3}.
Test: (1) g in A_Y, decided EXACTLY by Delta_Y^{2K} g in A_Y^+ with K = ceil(max(0,-inf g)/2)
      (proof: the coprime left fraction a^{-1}b of g in A^+ is unique; for g in A_Y it has a, b in A_Y^+,
      because A_Y^+ is closed under divisors in A^+; a right-divides Delta^{-inf g}, so sup(a) <= -inf g, and
      sup_{A_Y}(a) = sup_A(a) since normal forms of A_Y^+ elements agree in A_Y and A; hence Delta_Y^{2K} a^{-1}
      is positive in A_Y^+);
      (2) g in P_Y lies in F iff forgetting strand 1 gives the trivial pure braid on 3 strands (Garside in A_2).
Why this decides the vertex criterion: rho_X (Godelle-Paris retraction, a homomorphism on P, identity on P_X,
trivial on F) gives  c in F.P_X  iff  c rho_X(c)^{-1} in F; for c a P_X-conjugate of an F-element rho_X(c) = 1,
so  c in F.P_X  iff  c in F  (and likewise for P_X.F)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
for p in (os.path.join(HERE, '..', 'h4-artin-complex-6cycles-2026-09-17'),
          os.path.join(HERE, '..', '..', '..', 'w11-042', 'lib')):
    if os.path.exists(os.path.join(p, 'garside.py')):
        sys.path.insert(0, p)
        break
from garside import Coxeter, Artin

W4 = Coxeter(4, {(0, 1): 3, (1, 2): 3, (2, 3): 5})
G = Artin(W4)
W3 = Coxeter(2, {(0, 1): 3})
G3 = Artin(W3)
MY, MX, MZ = 0b0111, 0b1110, 0b0110
DY = G.simple(W4.parabolic_w0(MY))
DYW = [i + 1 for i in W4.word[W4.parabolic_w0(MY)]]


def inv(w):
    return [-g for g in reversed(w)]


def nf(w):
    return G.word(w)


def in_Y(g):
    """exact: return a positive Y-word u (list of letters) with g = Delta_Y^{-2K} u, or None if g not in A_Y"""
    k = g[0]
    K = max(0, -k + 1) // 2
    h = g
    for _ in range(2 * K):
        h = G.mul(DY, h)
    if h[0] != 0 or any(W4.supp[x] & ~MY for x in h[1]):
        return None
    u = []
    for x in h[1]:
        u += [i + 1 for i in W4.word[x]]
    return inv(DYW) * (2 * K) + u if K else u


def forget1(word):
    """B_4 word (letters +-1..3) -> B_3 word after deleting the strand starting at position 1"""
    pos = 1
    out = []
    for l in word:
        i = abs(l)
        if pos in (i, i + 1):
            pos = i + 1 if pos == i else i
            continue
        j = i if i < pos else i - 1
        out.append(j if l > 0 else -j)
    return out


def in_F(w):
    """w: pure H_4 word.  Exact decision of w in F."""
    u = in_Y(nf(w))
    if u is None:
        return False
    return G3.word(forget1(u)) == G3.one


P3, P2, P1 = [1, 1], [1, 2, 2, -1], [1, 2, 3, 3, -2, -1]

if __name__ == '__main__':
    X0 = [4, 4]
    tests = [('p1', P1), ('p2', P2), ('p3', P3), ('p1p2^-1p3', P1 + inv(P2) + P3), ('s4^2', X0),
             ('s2^2', [2, 2]), ('x0 p3 x0^-1', X0 + P3 + inv(X0)), ('x0 p2 x0^-1', X0 + P2 + inv(X0)),
             ('x0 p1 x0^-1', X0 + P1 + inv(X0)), ('s2^2 p1 s2^-2', [2, 2] + P1 + [-2, -2]),
             ('p1 s2^2', P1 + [2, 2])]
    for n, w in tests:
        print(n, in_F(w))
