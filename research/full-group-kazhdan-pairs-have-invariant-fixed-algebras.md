---
rg: 2
id: full-group-kazhdan-pairs-have-invariant-fixed-algebras
kind: claim
title: In the full group of a sofic free action, a Kazhdan infranormal pair has an invariant fixed-point algebra
distinct_from:
  kun-thom-free-nonsofic-action: that is the Kun--Thom nonsofic action of the Kun--Thom group itself; this puts the pair inside the full group of an action of an arbitrary group
  free-action-containing-nonsofic-group-relation-is-nonsofic: that needs a free action of a nonsofic group inside the relation; here the subgroup of the full group acts non-freely and is sofic
  groups-containing-kun-thom-pair-have-nonsofic-actions: that needs the pair as a subgroup of the acting group; here it sits only in the full group, as piecewise group elements
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**ESTABLISHED (unreviewed), conditional on Kun--Thom Theorem 4.1** (arXiv:2608.06222, unrefereed, verbatim in
the artifact).

Let `G` be a countable group and `a = G ↷ (X, μ)` a free p.m.p. action that is sofic in Păunescu's sense.
Let `R = R_a` be its orbit relation, and let `[R]` be its full group.

Let `Γ ≤ H ≤ [R]` be countable subgroups such that:

* `H` and `Γ` have property (T);
* `Γ` is infranormal in `H`, i.e. `P_Γ = {h ∈ H : hΓh⁻¹ ≤ Γ}` generates `H`.

Then the fixed-point algebra `L^∞(X)^Γ` is `H`-invariant.

The statement does not need `H` to embed in `G`, and it does not need `H ↷ X` to be free. It also holds for any
homomorphism `θ : H → [R]` of a Kun--Thom pair, because images of Kazhdan groups are Kazhdan and `θ(P_Γ) ⊆ P_{θΓ}`.

**Consequence (contrapositive).** Suppose some group `G` has a free p.m.p. action `a`, together with a pair
`Γ ≤ H ≤ [R_a]` as above, such that `L^∞(X)^Γ` is not `H`-invariant. Then `a` is not sofic, so `G ∉ 𝒮`.

For the Kun--Thom group `G_KT` this recovers `kun-thom-free-nonsofic-action`: take `a = b × Bernoulli`, where `b` is
the generalized Bernoulli action, and `H = G_KT`. For `SL_3(Z)` it is the reduction
`sl3z-nonsofic-from-full-group-kun-thom-violation`.

Proof: `full-group-kazhdan-pairs-have-invariant-fixed-algebras-proof`, which is internal apart from Theorem 4.1.
It has three steps:

1. Round the image of `[R]` to permutations.
2. Tensor with a free sofic representation of `H`.
3. Encode each `Γ`-invariant projection as a swap permutation on a doubled space, which lies in the centralizer.

The artifact also calibrates the statement and records no-go results for three seed families.
