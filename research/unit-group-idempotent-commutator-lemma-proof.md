---
rg: 2
id: unit-group-idempotent-commutator-lemma-proof
kind: route
title: Le Boudec–Matte Bon's proof of the commutator lemma, run with idempotents, orthogonality and compressions in place of subsets, disjointness and restrictions
target: unit-group-confined-subgroups-idempotent-commutator-lemma
requires: []
---

**Source of the argument.** Le Boudec–Matte Bon, arXiv:2006.08677, §3.2–3.4: the proofs of their Lemmas on `A_{σ,k}`, `B_λ` and `A^ρ_{σ,k}`, their Proposition, and Theorem 3.17. The TeX was read on MSI, l.512–694. The full line-by-line transfer is in `research/artifacts/sk-cstar-idempotent-2026-09-13-part1.md` §2.

**Dictionary.**
- Disjoint subsets ↔ orthogonal idempotents.
- `σ(Ω)` ↔ `σEσ^{-1}`.
- Supported in `⋃Ω_i` and preserving each `Ω_i` ↔ `g − 1 = Σ_i E_i(g−1)E_i` for pairwise orthogonal `E_i`.
- Restriction ↔ compression `p_E(g) = EgE` on `Stab(E)`.
- Elements supported in orthogonal idempotents commute (`xy = yx = 0`).
- An element supported in `E` is determined by `p_E`.

**Key verification.** For fixed `σ`, write `P = M_σ ⊔ F_σ` (by (C3)). Every support list used in the proof consists of idempotents from
`{E_α} ∪ {σ^{-1}E_ρσ : ρ ∈ M_σ} ∪ {σE_ρσ^{-1} : ρ ∈ M_σ}`,
and any two idempotents in one list, or in the two lists of the Claim, are equal or orthogonal:
- (C1), for the `E_α`;
- the definition of `M_σ`, for `σE_ρσ^{-1}` against `E_α`;
- for `σ^{-1}E_ρσ` against `E_α`: when `α ∈ M_σ`, conjugate `E_ρ ⊥ σE_ασ^{-1}`; when `α ∈ F_σ`, use `σ^{-1}E_ασ = E_α ≠ E_ρ`;
- conjugation, for pairs of translates;
- (C4), for `σE_σσ^{-1}` against `σ^{-1}E_ασ`, the only mixed pair in the Claim.

So each group element in the proof is block diagonal over one pairwise orthogonal family. Every set-theoretic step then becomes an identity of compressions:
- the commutator `[a,h]` of two block-diagonal elements that share only the block `E_ρ` equals `1 − E_ρ + [p_ρ(a), p_ρ(h)]`;
- the other steps are the same formal group theory as in the source: Neumann's covering lemma, the index estimates, FC-triviality.

The rigid groups are used only through being supported in `E_σ`, so any chosen subgroups `R_σ` work.

**Corollary.** `N` is normalized by a subgroup of index `≤ r` in `R_ρ`. An infinite simple group has no proper finite-index subgroups, so `N ⊴ R_ρ` and `N = R_ρ`.
