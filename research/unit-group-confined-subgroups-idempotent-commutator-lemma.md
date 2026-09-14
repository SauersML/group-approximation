---
rg: 2
id: unit-group-confined-subgroups-idempotent-commutator-lemma
kind: claim
title: "Commutator lemma for confined subgroups of unit groups: with an idempotent displacement configuration, a confined subgroup contains a nontrivial subgroup of a rigid group with finite-index normalizer"
artifacts:
  - research/artifacts/sk-cstar-idempotent-2026-09-13-part1.md
distinct_from:
  confined-subgroup-commutator-lemma: that is Le Boudec–Matte Bon's statement for permutation groups with subsets as supports; this is its transfer to unit groups of rings, with idempotents as supports and orthogonality as disjointness, and with arbitrary chosen rigid subgroups
---

**ESTABLISHED (unreviewed).**

Let `M` be a unital ring and `L = M^×`.
- `g ∈ L` is *supported in* an idempotent `E` if `g − 1 ∈ EME`.
- `g` is *trivial on* `E` if `gE = Eg = E`.
- `E ⊥ F` means `EF = FE = 0`.

Let `G, H ≤ L`, with `H` confined by `G`, `P` a confining subset, and `r = |P|`. Let `{E_σ}_{σ∈P}` be nonzero idempotents, and `R_σ ≤ G` nontrivial subgroups of elements supported in `E_σ`, with `R_σ = R_ρ` when `E_σ = E_ρ` and `FC_{≤r}(R_σ) = 1`. Suppose:
- (C1) `E_σ = E_ρ` or `E_σ ⊥ E_ρ`;
- (C3) `σ` is trivial on `E_ρ`, or `σE_ρσ^{-1} ⊥ E_α` for all `α`;
- (C4) `σE_σσ^{-1} ⊥ E_α` and `σE_σσ^{-1} ⊥ σ^{-1}E_ασ` for all `α`.

Then some `ρ ∈ P` has a nontrivial `N ≤ H ∩ R_ρ` whose normalizer in `R_ρ` has index at most `r`.

**Corollary.** If every `R_σ` is infinite and simple, then `H ⊇ R_ρ` for some `ρ`. So if the `R_σ` are nonamenable, `H` is not amenable.

**Proof:** `unit-group-idempotent-commutator-lemma-proof`.
