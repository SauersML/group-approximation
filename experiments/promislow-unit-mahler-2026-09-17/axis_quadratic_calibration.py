#!/usr/bin/env python3
"""Calibration of the axis-quadratic reduction on Gardam's unit.

Checks, exactly in R[P] with R = Z[s,t]/(s^4+1, t^4+1) (Gardam's unit alpha, inverse beta):
  1. psi: a -> b, b -> ab extends to an automorphism of P (relators map to 1 in the affine model), and
     psi(x) = y, psi(y) = z, psi(z) in {x, x^-1}.
  2. v_g = alpha g beta satisfies v^2 - (g + g^-1) v + 1 = 0 for g = x, y, z, and v_g is not in {g, g^-1}.
  3. supports of v_x, v_y, v_z; supports and coefficient ranges after specialising s=t=1 mod 2 (F_2[P]).
  4. the Mahler measure of v_x's fibre spectrum is 0 (max log|lambda| over random characters, zeta_8 embedding).
"""
import os, sys, math, cmath, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fibre_spectra as FS
G = FS.G
w = G.w

# 1. automorphism psi
def psi_word(word):
    img = {"a": [G.b], "b": [G.a, G.b], "A": [G.B], "B": [G.B, G.A]}
    out = G.E
    for ch in word:
        for g in img[ch]:
            out = G.mul(out, g)
    return out
assert psi_word("Bb") == G.E and psi_word("aA") == G.E
rel1 = "B" + "aa" + "b" + "aa"      # b^-1 a^2 b a^2
rel2 = "A" + "bb" + "a" + "bb"      # a^-1 b^2 a b^2
print("psi relators trivial:", psi_word(rel1) == G.E, psi_word(rel2) == G.E)
px, py, pz = psi_word("aa"), psi_word("bb"), psi_word("abab")
print("psi(x)==y:", px == G.y, " psi(y)==z:", py == G.z, " psi(z) in {x, X}:", pz in (G.x, G.X),
      "(=x)" if pz == G.x else "(=X)")
# psi is onto: a, b in image
# b = psi(a); a = psi(b) psi(a)^-1
print("psi onto (a = psi(b) psi(a)^-1):", G.mul(psi_word("b"), G.inv(psi_word("a"))) == G.a)

one = {G.E: {(0, 0): 1}}
def mono(g): return {g: {(0, 0): 1}}
def neg(U): return {g: {k: -v for k, v in c.items()} for g, c in U.items()}

res = {}
for name, g, gi in (("x", G.x, G.X), ("y", G.y, G.Y), ("z", G.z, G.Z)):
    v = G.gmul(G.gmul(G.alpha, mono(g)), G.beta)
    c = G.gadd(mono(g), mono(gi))
    q = G.gadd(G.gmul(v, v), neg(G.gmul(c, v)), one)
    triv = v in (mono(g), mono(gi))
    # F_2 reduction: s, t -> 1, coefficients mod 2
    f2 = {h: sum(cc.values()) % 2 for h, cc in v.items()}
    f2supp = sum(1 for val in f2.values() if val)
    coefsizes = sorted({abs(val) for cc in v.values() for val in cc.values()})
    print(f"v_{name} = alpha {name} alpha^-1: quadratic == 0: {q == {}} | trivial: {triv} | |supp| = {len(v)} "
          f"| |supp mod 2| = {f2supp} | |coeff| values {coefsizes}")
    res[name] = v

# 4. fibre spectrum of v_x
z8 = cmath.exp(1j * math.pi / 4)
comp = FS.compile_elem(FS.to_complex(res["x"], z8))
mx, m = FS.stats(comp, n=1500)
compa = FS.compile_elem(FS.to_complex(G.alpha, z8))
mxa, ma = FS.stats(compa, n=1500)
print(f"alpha: max log|lam| = {mxa:.4f}, m ~ {ma:.4f};  v_x: max log|lam| = {mx:.2e}, m ~ {m:.2e}")
print("DONE")
