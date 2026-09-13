---
rg: 2
id: relative-lemma-b-uniqueness-excludes-af-killing
kind: claim
title: The uniqueness hypothesis of relative Lemma B excludes killing by any AF-valued map that does not kill a projection outside the finiteness ideal, and is impossible at stably finite levels
distinct_from:
  bk-relative-lemma-b: that is the open ideal-relative killing tool; this shows its uniqueness hypothesis rules out AF targets and cannot hold at stably finite levels once a projection lies outside the finiteness ideal.
  bk-relative-boundary-descends-or-is-positively-detected: that shows the filtration route is blocked through infinite quotients; this blocks every AF target, equivariant or not, under the uniqueness hypothesis.
artifacts:
  - research/artifacts/bk-af-killing-projection-traces-2026-09-13.md
---

**ESTABLISHED (Corollary C of the artifact; lane proof, not externally
reviewed).**  Take `A, G, I, τ` as in `bk-relative-lemma-b`, and read its
hypothesis (3) as (3′): every lower semicontinuous trace on `A` that annihilates
`G` on its finiteness ideal and is finite and nonzero somewhere is a positive
multiple of `τ`.  Suppose some projection `P ∈ M_n(A)` is not in `M_n(I)`.

1. Every *-homomorphism `φ` of `A` into an AF algebra with `φ_*(G) = 0` has
   `φ(P) = 0`.  So no faithful embedding into an AF algebra kills `G`, whether or
   not it respects `I`.
2. `A` is not an ideal of a separable exact stably finite algebra with `G` its
   boundary subgroup.  So at the top level of a Blackadar–Kirchberg
   counterexample, and at every level `R/J` with `E/J` stably finite, (3′) forces
   every projection over `A` into `M_∞(I)`.

Mechanism: `(Tr ⊗ τ)(P) = ∞`.  Theorem A (case 1) or Proposition B (case 2)
gives an annihilating trace with `σ(P) = 1`, which is not a multiple of `τ`.

Meaning for the ideal-equivariant realisation.  Under uniqueness, a killing
embedding must go into a quasidiagonal algebra whose quotients carry `K_1`, so
that index maps, not traces, absorb the boundary.  In the real rank zero case the
uniqueness regime is empty, and the question becomes whether the trace condition
at every projection suffices for AF killing.
