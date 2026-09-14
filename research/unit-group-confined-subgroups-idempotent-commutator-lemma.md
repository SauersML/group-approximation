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

**Review (sk-verify-16, 2026-09-14): PASS-WITH-FIXES.** Re-derived against Le Boudec–Matte Bon arXiv:2006.08677v4 §3 (PDF pp. 10–16: Def 3.7/3.8/3.14, Remark 3.15, Lemmas 3.10/3.11/3.16/3.18, the Claim of Prop 3.20, Thm 3.19/3.21).
- Every support family is pairwise orthogonal under (C1),(C3),(C4): {E_α} ∪ {σ⁻¹E_ρσ}_{M_σ} (incl. F_σ ∩ M_σ = ∅ from nonzero idempotents); {E_ρ, σE_ρσ⁻¹}_{M_σ}; and the Claim family {E_ρ} ∪ {σ⁻¹E_ασ} ∪ {E_α} ∪ {σE_σσ⁻¹}, which uses both halves of (C4).
- [a,h] = 1 − E_ρ + [p_ρ(a),p_ρ(h)] ∈ H ∩ R_ρ, and chosen rigid subgroups suffice.
Fixes: cite v4 numbering (Theorem 3.19 with n = 1; Theorem 3.17 is the numbering of the restatement in arXiv:2012.03997), and justify trivial FC-center of infinite simple groups (FC-center all ⇒ f.g. normal closure is an FC-group, virtually abelian). See `research/artifacts/sk-verify-16-2026-09-13-part5.md` §2.
