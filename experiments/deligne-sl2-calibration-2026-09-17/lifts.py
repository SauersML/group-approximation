"""Presentation of SL_2(Z[1/2]) = SL_2(Z) *_{Gamma^0(2)} a SL_2(Z) a^-1 (Serre, Trees II.1.4) with the lift
exponents k_r of every relator in the universal cover G~ of SL_2(R), so r = z^(k_r) in G~, z = generator of pi_1.

Elements of G~ are pairs (M, f0): M in SL_2(R) and f0 = F(0), F the lift to R of the action of M on ray angles.
Generators (words read left to right, product = matrix product):
  x  = (S, pi/2)          S = [[0,-1],[1,0]]      x^4 = z
  y  = lift of ST with y^3 = x^2                 ST = [[0,-1],[1,1]]
  x' = a x a^-1, y' = a y a^-1                   a = diag(sqrt2, 1/sqrt2), a~ = (a, 0)
Run: python3 lifts.py   (prints the relators, checks them exactly in SL_2(Z[1/2]) and prints k_r)
"""
import math
from fractions import Fraction as Fr
import numpy as np

TWO_PI = 2 * math.pi

def ang(v):
    return math.atan2(v[1], v[0])

class Lift:
    def __init__(self, M, f0):
        self.M = np.array(M, dtype=float); self.f0 = float(f0)
    def F(self, phi):
        k = math.floor(phi / TWO_PI); r = phi - k * TWO_PI
        w = self.M @ np.array([math.cos(r), math.sin(r)])
        d = (ang(w) - self.f0) % TWO_PI if r > 0 else 0.0
        return self.f0 + d + k * TWO_PI
    def __mul__(self, o):
        return Lift(self.M @ o.M, self.F(o.F(0.0)))
    def inv(self):
        Mi = np.linalg.inv(self.M)
        # F^-1(0): the phi with F(phi) = 0; F^-1(0) = angle of Mi e1 on the branch with F(that) = 0
        a0 = ang(Mi @ np.array([1.0, 0.0]))
        for k in range(-5, 6):
            c = a0 + k * TWO_PI
            if abs(self.F(c)) < 1e-9:
                return Lift(Mi, c)
        raise RuntimeError("no inverse branch")

def z_power(g):
    """g must lie over +-I or I; return the rotation amount F(0)/(2 pi) (z = 1, x^2 = 1/2)."""
    return g.f0 / TWO_PI

S = [[0, -1], [1, 0]]; ST = [[0, -1], [1, 1]]
x = Lift(S, math.pi / 2)
x2 = x * x
# choose y over ST with y^3 = x^2 (f0 = angle of ST e1 = pi/2 plus branch)
y = None
for k in range(-3, 4):
    c = Lift(ST, math.pi / 2 + k * TWO_PI)
    c3 = c * c * c
    if np.allclose(c3.M, x2.M) and abs(c3.f0 - x2.f0) < 1e-9:
        y = c
assert y is not None
s2 = math.sqrt(2.0)
A = Lift([[s2, 0], [0, 1 / s2]], 0.0)
Ai = A.inv()
xp = A * x * Ai; yp = A * y * Ai
GEN = {"x": x, "y": y, "X": xp, "Y": yp}

def ev(word):
    """word: list of (gen, +-1)"""
    g = Lift(np.eye(2), 0.0)
    for s, e in word:
        h = GEN[s] if e == 1 else GEN[s].inv()
        g = g * h
    return g

def w(s):
    """parse 'x y^-1 X^2' style words"""
    out = []
    for tok in s.split():
        if "^" in tok:
            b, e = tok.split("^"); e = int(e)
        else:
            b, e = tok, 1
        out += [(b, 1 if e > 0 else -1)] * abs(e)
    return out

RELATORS = {
    "x4": w("x^4"),                                  # SL_2(Z): x^4 = 1 (lifts to z)
    "xy": w("x^2 y^-3"),                             # SL_2(Z): x^2 = y^3
    "XY": w("X^2 Y^-3"),                             # conjugate copy
    "xX": w("x^2 X^-2"),                             # -I identified
    "T":  w("x^-1 y x^-1 y") + w("Y^-1 X"),          # T^2 (in A) = a T a^-1 (in B)
    "U":  w("x^-1 y^-1 x x") + w("Y X^-1 Y X^-1"),  # U = a U2 a^-1, U2 = S T^-2 S^-1
}

# exact check in SL_2(Z[1/2]) with Fractions
def mat(Mf):
    return [[Fr(v) for v in r] for r in Mf]
def mm(P, Q):
    return [[sum(P[i][k] * Q[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def minv(P):
    return [[P[1][1], -P[0][1]], [-P[1][0], P[0][0]]]
aM = [[Fr(2), Fr(0)], [Fr(0), Fr(1)]]   # conjugation by diag(sqrt2,1/sqrt2) = conjugation by diag(2,1) in PGL
aMi = [[Fr(1, 2), Fr(0)], [Fr(0), Fr(1)]]
EX = {"x": mat(S), "y": mat(ST)}
EX["X"] = mm(mm(aM, EX["x"]), aMi); EX["Y"] = mm(mm(aM, EX["y"]), aMi)
def exact(word):
    P = mat(np.eye(2).astype(int).tolist())
    for s, e in word:
        P = mm(P, EX[s] if e == 1 else minv(EX[s]))
    return P

def k_of(word):
    g = ev(word)
    assert np.allclose(g.M, np.eye(2), atol=1e-9), g.M
    k = z_power(g)
    assert abs(k - round(k)) < 1e-9
    return int(round(k))

K = {}
for name, word in RELATORS.items():
    P = exact(word)
    assert P == [[1, 0], [0, 1]], (name, P)
    K[name] = k_of(word)

if __name__ == "__main__":
    print("y.f0/(2pi) =", y.f0 / TWO_PI)
    Tx = ev(w("x^-1 y"))
    print("x^-1 y lies over T:", np.round(Tx.M, 6).tolist(), " F(0)/(2pi) =", Tx.f0 / TWO_PI,
          "(canonical unipotent lift has F(0) = 0)")
    print("X Y exact:", EX["X"], EX["Y"])
    for name in RELATORS:
        print(f"relator {name:3s}: exact in SL_2(Z[1/2]); lift exponent k = {K[name]}")
