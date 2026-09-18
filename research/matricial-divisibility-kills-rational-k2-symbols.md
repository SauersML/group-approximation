---
rg: 2
id: matricial-divisibility-kills-rational-k2-symbols
kind: claim
title: If R ≅ M_n(R_n) as unital rings for n divisible by every integer, then K_2(Q) -> K_2(R) is zero
distinct_from:
  rational-leavitt-path-k1-k2-scalar-dichotomy: that shows the image of K_2(Q) is infinitely generated for Leavitt path algebras with [1] of infinite order; this gives a ring-theoretic condition under which the image vanishes.
  infinitely-generated-symbols-block-fp-elementary-groups: that is the obstruction (finitely presented E_N forces finitely generated symbols); this removes the rational part of it.
  rational-k1-detection-forces-infinite-order-unit-class: that is the (K1) necessary condition; this is a sufficient condition for the rational part of (K2).
  rational-eigenvalue-iff-subshift-ring-is-matrix-ring: that realizes R ≅ M_p(S) for subshift crossed products over F_q; this uses such matrix decompositions over rings containing Q.
---

**ESTABLISHED** by `matricial-divisibility-kills-rational-k2-symbols-proof`
(lane proof from two textbook facts; see the proof for its trust surface; not independently
reviewed).

## Statement

Let `R` be a unital ring with a unital map `Q -> R`. Suppose that for every `t >= 1` there are
an `n` with `t | n`, a unital ring `R_n` and a unital ring isomorphism `R ≅ M_n(R_n)`. Then the
induced map `K_2(Q) -> K_2(R)` is zero. In particular every rational Steinberg symbol
`{λ, μ}`, with `λ, μ ∈ Q^x`, vanishes in `K_2(R)`.

## Scope

- **Satisfied by `U_Q = colim M_(n!)(Q)`**, which is the mechanism of the UHF K-budget.
- **Not a sufficient condition for the budget.**
  - The (K1) half still needs `ker(Q^x -> K_1(R))` finitely generated, so `[1]` must also have
    infinite order (`rational-k1-detection-forces-infinite-order-unit-class`).
  - The symbols `{λ, x}` for non-rational units `x` are untouched. Laurent units kill every
    skew Laurent ring (`laurent-rational-symbols-block-fp-elementary-groups`).
- **Finitely generated examples of the hypothesis exist in characteristic `p`.** Subshift
  crossed products with a full odometer factor satisfy
  `rational-eigenvalue-iff-subshift-ring-is-matrix-ring`. What is missing is a finitely
  generated one containing `Q` with no Laurent-type unit.
- **Candidate (2026-09-18, lane `gq-deep-adelic-1`, unrefereed).**
  `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`: a ring over an `SL_3(Z)` Toeplitz
  subshift that is finitely generated and simple, with centre `Q` and `Λ_N ⊆ {±1}`. It is
  matricially divisible along the congruence blocks, so this claim kills `K_2(Q)` at its unit.
  Whether it meets the whole budget is `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`,
  which is open: every full corner has to pass `full-corners-must-kill-rational-k2-symbols`,
  and every unit has to be checked.
