---
rg: 2
id: confined-subgroup-commutator-lemma
kind: claim
title: "Le Boudec–Matte Bon commutator lemma: a confined subgroup contains a nontrivial subgroup of a rigid stabilizer with finite-index normalizer"
distinct_from:
  full-group-confined-subgroups-are-finite-set-stabilizers: that claim classifies the confined subgroups of topological full groups of minimal effective groupoids; this claim is the general commutator lemma for confined subgroups of permutation groups admitting displacement configurations
---

**ESTABLISHED (import).**

For `G ≤ Sym(Ω)` and `Σ ⊆ Ω`, the rigid stabilizer `R_G(Σ)` is the pointwise
fixator in `G` of `Ω \ Σ`. A subgroup `H ≤ G` is confined (by `G`) if some
finite `P ⊆ G \ {1}` meets every conjugate `gHg^{-1}`, `g ∈ G`. For a finite
set `P` of nontrivial permutations, a family `{Ω_σ}_{σ∈P}` of nonempty subsets
is a displacement configuration if:

1. `Ω_σ = Ω_ρ` or `Ω_σ ∩ Ω_ρ = ∅`, for all `σ, ρ`;
2. `σ` fixes `Ω_ρ` pointwise or `σ(Ω_ρ)` is disjoint from `⋃_α Ω_α`, for all
   `σ, ρ`;
3. `σ(Ω_σ)` is disjoint from `⋃_α Ω_α` and from `⋃_α σ^{-1}(Ω_α)`, for all `σ`.

**Theorem (commutator lemma).** Let `H, G ≤ Sym(Ω)` with `H` confined by `G`,
`P` a confining subset, and `r = |P|`. Assume `{Ω_σ}_{σ∈P}` is a displacement
configuration for `P` such that, for every `σ ∈ P`, `R_G(Ω_σ)` is nontrivial
and every nontrivial conjugacy class of `R_G(Ω_σ)` has more than `r` elements.
Then there is `ρ ∈ P` such that `H` contains a nontrivial subgroup
`N ≤ R_G(Ω_ρ)` whose normalizer in `R_G(Ω_ρ)` has index at most `r`.

**Existence of configurations.** If `X` is a Hausdorff space without isolated
points and `σ_1, …, σ_q` are homeomorphisms of `X` with every `σ_i^2`
nontrivial, then `{σ_1, …, σ_q}` has a displacement configuration consisting
of open subsets of `X`.

**Proof:** `confined-subgroup-commutator-lemma-citation`.
