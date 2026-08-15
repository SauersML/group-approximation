---
rg: 2
id: infinite-cyclic-compression-lamp-mf-proof
kind: route
title: Slow bumps at separated finite-quotient sites represent the integer lamps
target: infinite-cyclic-compression-lamp-mf
requires: []
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
  - GroupApproximation/Sofic/IntegerLampSurvival.lean
---

## Direct proof

Enumerate the sites `X = {x_1, x_2, ...}` with representatives
`r_j in H`, `x_j = r_j L_1`, and enumerate the nonidentity elements of
`H`.  Fix a finite symmetric generating set `T` of `L_1` and a real
`alpha` with `alpha/(2 pi)` irrational.

**Quotient selection.**  For each `n`, residual finiteness supplies a
finite quotient `q_n : H -> F_n` such that (1) the first `n` nonidentity
elements of `H` survive, and (2) for all `i != j <= n`, the element
`q_n(r_j^{-1} r_i)` is not a `q_n(T)`-word of length at most `3n` — each
such constraint excludes finitely many nonidentity elements
`r_j^{-1} r_i w^{-1}` (nonidentity because `r_j^{-1} r_i notin L_1`), so
one quotient handles all of them.  As always
`K_n := q_n(L_1) = q_n(L)` by finite-cardinality cancellation.

**The model.**  Let `ell_n` be `q_n(T)`-word length on `K_n`, and
`f_n(y) = max(1 - ell_n(y)/n, 0)` on `K_n`, zero outside.  On
`l^2(F_n)`: `R_n` the right regular representation of `H` through `q_n`,
and the root-lamp generator represented by the diagonal
`V_n : delta_y -> exp(i alpha f_n(y)) delta_y`.  Site lamps are the
conjugates `Theta(r) v Theta(r)^*` for `x = r L_1`, where `v = [V_n]` and
`Theta = [R_n]`.

**Covariance and exact relations in the corona.**  For `h in L_1`, right
multiplication by `q_n(h)` preserves `K_n` and shifts `ell_n` by at most
the `T`-length `m(h)`, so `‖R_n(h) V_n R_n(h)^* - V_n‖ <= |alpha| m(h)/n
-> 0`: the site lamp is independent of the coset representative in the
corona, and the family is exactly `H`-equivariant.  Diagonal operators
commute, so distinct site lamps commute and each site copy of `Z` is
represented exactly (powers of a diagonal).  All defining relations of
`Z^(X) semidirect H` therefore hold exactly in the corona, giving a
homomorphism `Phi`.

**Faithfulness.**  For a nonzero base element `a = sum_{j in J} m_j
delta_{x_j}` pick `j_0 in J` with `m_{j_0} != 0`.  For `n` beyond
`max(J)`, evaluate the diagonal representative at the basis vector
indexed by `q_n(r_{j_0})^{-1}`: the `j_0`-bump contributes
`f_n(e) = 1`, while for `j != j_0` the argument is
`q_n(r_{j_0}^{-1} r_j)`-shifted and lies outside the radius-`n` ball by
property (2), so those bumps vanish.  The value is
`exp(i alpha m_{j_0}) != 1` by irrationality, so `a` survives at
operator-norm distance `|exp(i alpha m_{j_0}) - 1|`.  For an element with
nontrivial `H`-part, property (1) eventually makes its permutation part
nontrivial; a diagonal times a fixed-point-free-on-some-point permutation
moves a basis vector to an orthogonal one, keeping operator-norm distance
at least `sqrt 2`.  Hence `Phi` is injective, and dimension amplification
normalizes the coordinate sequence.

**Audit notes (this session).**  Checked: the coset-independence and
covariance estimates; the exactness of all wreath relations in the corona
(each relation involves finitely many generators, and every defect
vanishes in norm); the two-bump disjointness from the `3n`-separation; and
the two faithfulness estimates.  The lamp images have full-arc spectrum,
as `spectral-component-motion-bound` requires of surviving witnesses.

## Formalized layer (2026-08-15)

The locality layer of the survival statement is now kernel-checked in
`GroupApproximation/Sofic/IntegerLampSurvival.lean`: for any
permutation action, finite windows over residually finite levels with
finite orbits make the integer-lamp wreath operator-MF
(`isOperatorMF_lampWreath`, via window subgroups proved residually
finite by reduction modulo a large integer into the finite window
wreath), and the telescope instance
(`isOperatorMF_integerLampTelescope`) gives: with residually finite
base and finite-index compression, the integer-lamp-by-telescope group
— the infinite-cyclic analogue of the Clifford lamp kernel — is
operator-MF.  What remains paper-level is exactly the full `W_Z` with
the compressing shift adjoined: the shift destroys orbit locality, and
the slow-bump corona model above is the intended route; no locality
argument can reach it, since the analogous full Clifford group is
non-MF.  The formalized layer already witnesses the dichotomy at equal
footing: the SAME telescope layer carries the kernel-checked collapse
of order-two lamps (the sign-free quotient theorems), so finite-order
lamps die and integer lamps survive over one site space.
