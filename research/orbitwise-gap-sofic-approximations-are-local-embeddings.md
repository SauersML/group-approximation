---
rg: 2
id: orbitwise-gap-sofic-approximations-are-local-embeddings
kind: claim
title: Sofic approximations through permutation groups with an orbitwise fixed-point gap are local embeddings, and Kazhdan cut-downs of semisimple vector models have such a gap
distinct_from:
  gap-sofic-approximations-are-local-embeddings: that needs one fixed-point gap for every nontrivial element on the whole set; this needs the gap only on orbits where the element acts nontrivially, which covers non-transitive modules and invariant subsets, where a global gap fails.
  almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial: that turns a nontrivial almost action of an IRS-rigid simple group into a sofic approximation; this shows such an almost action cannot be a Kazhdan cut-down of a semisimple vector model unless the group is LEF.
  kazhdan-ergodic-sofic-centralizer-forces-lef: that derives LEF from an ergodic centralizer in the permutation ultraproduct; this derives LEF from property (T) of a cover and an orbitwise gap of the targets, with no centralizer hypothesis.
artifacts:
  - research/artifacts/sk-sofic-almost-action-plan-2026-09-14.md
---

**ESTABLISHED (unreviewed, lane sk-sofic-almost-action, 2026-09-14)** by route
`orbitwise-gap-sofic-approximations-local-embeddings-proof`.

**Definition.** `H ≤ Sym(Ω)`, with `Ω` finite, has an *orbitwise gap* `δ > 0` if, for every `x ∈ H` and every
`H`-orbit `O`, either `x` fixes `O` pointwise or `|Fix(x) ∩ O| ≤ (1−δ)|O|`.

**Theorem O.** A countable group is LEF iff it has a sofic approximation `σ_N : G → H_N ≤ Sym(Ω_N)` with a common
orbitwise gap.

**Family (E).** Let `𝒜` be a finite semisimple algebra over a finite field, `W` a finite unital `𝒜`-module and
`n ≥ 1`. Then `EL_n(𝒜)` and `GL_n(𝒜)`, acting on `W^n`, have orbitwise gap `1/2`.

**Kazhdan cutting lemma.** Let `H` have Kazhdan pair `(A,κ)`, let `X` be a finite `H`-set, and let `Y ⊆ X` with
`|aY Δ Y| ≤ ε|Y|` for `a ∈ A`. Then an `H`-invariant `Z ⊆ X` has `|Y Δ Z| ≤ (2|A|/κ²)ε|Y|`.

**Corollary C (cut-downs).** Let `G = H/K` with `H` Kazhdan. Let `ρ_N : H → GL(X_N)` have images with a common
orbitwise gap, for example `ρ_N(H) = EL_n(𝒜_N)` on `W_N^n` with `𝒜_N` semisimple. Let `Y_N ⊆ X_N` be
`ε_N`-almost invariant with `ε_N → 0`, and let `σ_N` complete the partial maps `a|_(Y_N ∩ a^(−1)Y_N)` to
permutations.
- If `σ_N` is a sofic approximation of `G` (relators almost trivial, nontrivial elements almost fixed-point free),
  then `G` is LEF.
- For an IRS-rigid infinite simple `G`, it suffices that `σ_N` satisfies (AF1) and `|Fix_N| ≤ (1−c)|Y_N|`.

**For the hosts.** Take `H = EL_n(F_2⟨A⟩)` (Kazhdan, Ershov–Jaikin) and `G = G_Δ`, marked by the `e_ij(1)` and the
`e_ij` of the letters. `G_Δ` is LEF iff `Δ` is. So for sofic non-LEF `Δ`:
- no almost-invariant set of vectors, in any sequence of semisimple `F_2`-linear models, carries an almost action
  certifying soficity of `G_Δ`;
- the same holds for `EL_3(F_2[Δ])`.

This covers every `ρ_N` whose image algebra is semisimple, for instance a full matrix algebra. Whether the image
algebras of the Theorem A models (`sofic-lamplighter-bernoulli-crossed-products-have-rank-models`) are semisimple is
not checked here.

**Model test.**
- *Orbitwise gap.* It fails for `Sym(m)` on points, since a transposition has `fpr → 1`. That is consistent: sofic
  non-LEF groups such as `BS(2,3)` use such targets. The gap theorem's families (affine, projective) are transitive,
  hence orbitwise.
- *(T) in the lemma.* It fails for `Z` on `Z/m` with `Y` an interval of length `m/2`: `ε = 4/m`, but the invariant
  sets are `∅` and `Z/m`. (T) is used only in the lemma.
- *Semisimplicity.* It is used only in Family (E). For algebras with a radical the orbitwise gap is not proved here
  and not known to fail (target T5 of the artifact).
- *Hosts.* Theorem L (`lamplighter-host-elementary-groups-are-character-rigid`, sk-verify-18 PASS) gives IRS rigidity.

**Credit.**
- Theorem O adapts the gap route of `gap-sofic-approximations-are-local-embeddings`.
- The cutting lemma is the standard Cheeger form of property (T).
- Family (E) is Wedderburn–Artin plus transitivity of `SL` on nonzero vectors.
- No novelty is claimed for the parts. What is new here is the combination closing Hamming-thin cut-downs.
- Bounded search: a grep of main for "orbitwise" and "almost invariant", with no matching claim.
