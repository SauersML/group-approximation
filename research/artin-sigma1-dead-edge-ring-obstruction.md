---
rg: 2
id: artin-sigma1-dead-edge-ring-obstruction
kind: claim
title: "Dead-edge rings: a nonzero ring in which the dead-edge sums across a vertex cut vanish proves that a character of an Artin group is outside Sigma^1"
distinct_from:
  artin-sigma1-living-subgraph-bounds: that records Meier's inclusions, which never see dead edges; this is a new non-membership criterion aimed at dead edges, with arbitrary non-commutative coefficients
  artin-sigma1-conjecture-known-families: that lists families where the conjecture is proved; this is a general tool, and it proves non-membership only when a ring witness exists
---

Let `A_Γ` be an Artin group and `χ : A_Γ -> Z` a nonzero character. Suppose:

- `V(Γ) = V_1 ⊔ V_2`, and each `V_i` contains a vertex with `χ(v) != 0`;
- every edge `e = {u, v}` with `u ∈ V_1`, `v ∈ V_2` is dead:
  `l(e) = 2k_e >= 4` and `χ(u) + χ(v) = 0`;
- there are a nonzero associative unital ring `R` and a homomorphism
  `ρ : A_Γ -> R^×` with `1 + ρ(uv) + ... + ρ(uv)^{k_e - 1} = 0` in `R` for every such edge.

Then `ker χ` is not finitely generated, and `[χ] ∉ Σ^1(A_Γ)`.

Proof sketch. Use twisted Laurent coefficients `S = R((t))`, `g ↦ t^{χ(g)} ρ(g)`.
(A) A finitely generated `ker χ` forces `H_1(A_Γ; S) = 0`: the conjugation relators
`τ n_i τ^{-1} = w_i` give the invertible matrix `t^{-1} ρ(τ)^{-1} I - J`.
(C) The functional `Φ(w) = Σ_{x ∈ V_1} w_x (t^{χ(x)} ρ(x) - 1)` kills every relator block
and maps `ker ∂_1` onto `S`. It kills a cross block because that block has the factor
`1 + ρ(uv) + ... + ρ(uv)^{k-1}`; so `H_1(A_Γ; S) != 0`. By symmetry `Σ^1(A_Γ) = -Σ^1(A_Γ)`,
and then `[χ] ∈ Σ^1` would make `ker χ` finitely generated. Full proof: artifact
`research/artifacts/zp-artin-sigma1-dead-edge-rings-2026-09-13.md`, §§1–4.

Scope. With `R = C` and `ρ` a finite abelian character, this is the hypothesis of
Escartín-Ferrer's Theorem 4.4 (arXiv:2501.08692v3). It allows any vertex partition
with dead cross edges, dead vertices on either side, and non-commutative `R`, for
example matrix rings. Non-commutative `R` is genuinely needed:
`artin-346-dead-character-outside-sigma1-by-rank-two-rep` versus
`artin-346-commutative-rings-miss-the-dead-cut`. The criterion is not always
available: `artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring`.

Status: UNREVIEWED (z1-06-bns-artin, 2026-09-13).
