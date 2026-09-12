---
rg: 2
id: rank-ultraproduct-unit-groups-solve-nonsingular-equations
kind: claim
title: Nonsingular one-variable matrix equations over an algebraically closed field of characteristic p have roots up to amplification, a scalar, and vanishing normalized rank
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that asks for exact roots in an overgroup of an arbitrary group; this asks for approximate roots, in normalized rank after amplification, of matrix equations over an algebraically closed field of characteristic p.
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

**OPEN.** Fix a prime `p` and let `Fbar` be an algebraically closed field of characteristic `p`.
- **Setting.** Take a word `c_0 t^(e_1) c_1 ... t^(e_l) c_l` with `e_1 + ... + e_l != 0`, coefficients
  `c_0, ..., c_l in GL_d(Fbar)`, and `eps > 0`.
- **Statement.** There are `k >= 1`, `t in GL_(dk)(Fbar)` and `lambda in Fbar^x` with
  `rank((c_0 (x) 1_k) t^(e_1) (c_1 (x) 1_k) ... t^(e_l) (c_l (x) 1_k) - lambda 1) <= eps dk`.

Equivalently, unit groups of rank ultraproducts over `Fbar`, modulo scalars, solve nonsingular equations after
amplification. This is the characteristic-`p` rank form of the Gerstenhaber--Rothaus root theorem.

**Payoff.** By `char-p-schur-radical-from-rank-root-solvability`, it puts the Schur kernel of every nonsingular
adjunction in the rank radical of central extensions by finite groups of order prime to `p`. With
`sp4-schur-kernel-meets-the-deligne-triple-class`, `E_3` would then not be `F_p`-linear sofic (artifact
Corollary 3.5).

## Attempts

- **Power words: solved.** `t^m = lambda c^(-1)` is solvable exactly after amplification, using the Jordan
  decomposition and, when `p` divides `m`, the similarity of `(1 + N_(ps))^p` with `p` Jordan blocks of size `s`
  (artifact Section 3.3).
- **Finite-field non-squares: harmless.** Exact roots can fail in `GL_d(F_q)`, but only at rank cost `1`, and over
  `Fbar` scalars have all roots.
- **Degree theory: no analogue.** The Gerstenhaber--Rothaus proof uses the degree of the word map on the compact
  manifold `U(d)`, which has no characteristic-`p` counterpart known here.
- **Algebraic dominance: too weak.** Over `C` the word map of `GL_d(C)` is dominant because its image contains
  `U(d)`, but that gives roots only for generic coefficient tuples and nothing uniform in `d`.
- **Twisted-cyclic reduction (w5-rgr-p).** Amplifying by `k = e` with a twisted cyclic shift `t` makes
  `w(t)` block-diagonal, reducing RGR_p to a cyclic scalar system `P_m = lambda 1` (`m mod e`) in the `e`
  twists `b_j in GL_d`; see `rgr-p-reduces-to-cyclic-twist-system` and artifact
  `research/artifacts/rgr-p-cyclic-twist-reduction-2026-09-12.md`. No loss: the system is equivalent to
  RGR_p at that amplification.
- **Scalar vs general-matrix targets (w5-rgr-p).** The `p`-divisibility Jordan subtlety above is confined
  to general-matrix targets. A scalar target `t^e = lambda 1` is solved exactly in every characteristic
  by the companion matrix of `x^e - lambda` (`scalar-target-power-words-have-exact-roots`), so pure power
  words are unconditionally clean.
- **Two-syllable solved (w5-rgr-p).** `c_0 t c_1 t c_2 = lambda 1` has the explicit exact solution
  `t = [[0, c_0^(-1) lambda c_2^(-1)], [c_1^(-1), 0]]` in `GL_(2d)`; the equal-exponent two-syllable word
  reduces to power words (`two-syllable-nonsingular-words-are-exactly-solvable`).
- **Where it stops (w5-rgr-p).** The `e` cyclic rotations are not mutually conjugate (the fixed `c_i` do
  not rotate), so the system does not collapse; and rank slack does not obviously help, because
  block-diagonality pins the cycle length to `e` (a longer shift makes `w(t) - lambda` nearly full rank).
  First open shapes: unequal-exponent two-syllable `c_0 t^(e_1) c_1 t^(e_2) c_2` (`e_1 != e_2`), and
  all-exponent-one `c_0 t c_1 ... t c_l` for `l >= 3`.
