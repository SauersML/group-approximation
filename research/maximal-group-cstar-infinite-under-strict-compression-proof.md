---
rg: 2
id: maximal-group-cstar-infinite-under-strict-compression-proof
kind: route
title: The Kazhdan projection is dominated strictly by its own conjugate
target: maximal-group-cstar-infinite-under-strict-compression
requires: []
artifacts:
  - GroupApproximation/Analysis/MaximalCStarParagraphEndpoint.lean
  - GroupApproximation/Analysis/MaximalCStarKazhdanAverage.lean
  - GroupApproximation/Analysis/KazhdanProjectionAbsorption.lean
  - GroupApproximation/Analysis/MaximalCStarLiteralBase.lean
---

## Direct proof, machine-checked

**The projection.**  Property `(T)` for the compressed vertex gives a spectral
gap for the averaging operator over a Kazhdan set, so the continuous functional
calculus produces a projection `p` in the maximal algebra that is the identity
on invariant vectors and zero on the gap side (`MaximalCStarKazhdanAverage`,
with the spectrum confinement `μ ≤ rate ∨ μ = 1` proved there).
`KazhdanProjectionAbsorption` gives `avg · p = p`.

**Domination.**  `t Γ t⁻¹ ≤ Γ` means the compressed vertex is contained in the
original, so its invariant vectors contain the original's; both products
`(u p u*) p` and `p (u p u*)` therefore collapse to `p`.  That is a
two-sided domination and needs no strictness.

**Strictness.**  This is where `⊊` is used: the quasi-regular coordinate at
the proper inclusion sees a vector invariant under `t Γ t⁻¹` and not under `Γ`,
so `u p u* ≠ p`.  A self-adjoint idempotent strictly dominated by a conjugate
of itself is exactly a non-Dedekind-finite witness -- `x* x = 1` with
`x x* ≠ 1` after normalizing -- and the remaining failures follow: no faithful
trace can be blind to it, so no faithful tracial state; not stably finite; not
RFD; `not_hasMFEmbedding` and `not_isMFAlgebra` from
`ProperProjectionCompression`.

**The reduced side.**  `ReducedGroupCStarTrace` supplies the canonical faithful
trace on the reduced algebra of a discrete group, and a faithful trace forbids
a proper projection compression -- so `IsEmpty (ProperProjectionCompression …)`
there, which is the contrast the claim records.

**Instantiation.**  `MaximalCStarLiteralBase` exhibits the strict Kazhdan
compression for the literal group, discharging the hypothesis at the concrete
witness.
