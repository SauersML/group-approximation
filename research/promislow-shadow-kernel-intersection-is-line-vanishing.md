---
rg: 2
id: promislow-shadow-kernel-intersection-is-line-vanishing
kind: claim
title: The three definite-shadow kernels of Z[P] meet in the coefficientwise ideal of the three lines through (-1,-1,-1)
distinct_from:
  promislow-integral-units-have-monomial-definite-line-shadows: that proves every unit of Z[P] is a signed monomial modulo each of the three kernels; this computes the intersection of those kernels explicitly.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture; this only describes where the residue-trivial units of Z[P] live.
---

**ESTABLISHED.** Let `P` be the Promislow group with `x = a^2`, `y = b^2`,
`z = (ab)^2`, `L = <x, y, z> = Z^3`, and put `X = x + 1`, `Y = y + 1`,
`Z = z + 1` in `Z[L]`. Every element of `Z[P]` is uniquely
`p + q a + r b + s ab` with `p, q, r, s in Z[L]` (coefficients on the left). Let
`I_A = (y+1, z+1)`, `I_B = (x+1, z+1)`, `I_C = (x+1, y+1)` be the two-sided
ideals of `promislow-integral-units-have-monomial-definite-line-shadows`.

1. `I_A = { p + q a + r b + s ab : p, q, r, s in (Y, Z) Z[L] }`, and likewise
   `I_B` with `(X, Z)` and `I_C` with `(X, Y)`.
2. `I_A cap I_B cap I_C = { p + q a + r b + s ab : p, q, r, s in (XY, XZ, YZ) Z[L] }`.
   Equivalently, each of `p, q, r, s`, viewed as a function on the torus
   `Hom(L, C^x)`, vanishes on the three lines `{y = z = -1}`, `{x = z = -1}` and
   `{x = y = -1}` (the ideal `(XY, XZ, YZ)` is the ideal of their union).
3. Consequently every unit `v` of `Z[P]` that is trivial modulo 2 (Tabei's Case A,
   after normalization) is `epsilon + p + q a + r b + s ab` with `epsilon = +-1`
   and `p, q, r, s in (XY, XZ, YZ) Z[L]`, by item 3 of
   `promislow-integral-units-have-monomial-definite-line-shadows`.

**Scope.** This is bookkeeping for Case A. It proves no triviality. Every
element `1 + XYZ f` lies in `1 + I_A cap I_B cap I_C`, and nothing here decides
which of those are units. No novelty is claimed.

DERIVATION
[[promislow-shadow-kernel-intersection-line-vanishing-proof]]
