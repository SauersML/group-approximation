---
rg: 2
id: projective-unitary-classes-vanish-on-schur-kernel
kind: claim
title: Projective unitary classes of the coefficients vanish on the Schur kernel of a nonsingular adjunction
invalidates: [schur-kernel-search-over-finite-coefficient-groups]
distinct_from:
  cdi-torsionization-needs-schur-multiplier-separation: that asks whether a given multiplier of a projective quotient annihilates the finite residual of its Schur multiplier; this proves that every projective unitary multiplier extends across a nonsingular one-variable adjunction and so vanishes on its Schur kernel.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `Q` be countable and `w in Q * <t>` nonsingular, with Schur kernel
`K_2(Q, w)` as in `nonsingular-adjunction-never-enlarges-schur-multiplier`.
Let `U = (prod_n U(d_n))/N` for any normal subgroup `N`, let `A` be the
image of the scalar sequences, and put `T = U/A`. For every homomorphism
`phi : Q -> T` the pulled-back multiplier

    beta_phi in H^2(Q; A) = Hom(H_2(Q; Z), A)

vanishes on `K_2(Q, w)`.

Consequently `K_2(Q, w) = 0` whenever such multipliers separate the points of
`H_2(Q)`. In particular `K_2(Q, w) = 0` for **every finite** `Q`: twisted
regular representations realize every class in `Hom(H_2 Q, U(1))`. The
target may be the operator-norm, normalized-HS or rank quotient, or any other.

DERIVATION
projective-schur-class-extension-proof
