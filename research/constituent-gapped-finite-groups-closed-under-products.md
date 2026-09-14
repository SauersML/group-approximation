---
rg: 2
id: constituent-gapped-finite-groups-closed-under-products
kind: claim
title: Finite groups whose irreducible representations are all theta-gapped form a class closed under direct products and quotients, containing abelian and quasisimple classical groups
distinct_from:
  fp-simple-groups-have-no-gapped-finite-unitary-models: that uses a groupwise gap at every noncentral element, which fails for direct products of nonabelian groups; this uses a gap only at elements that are non-scalar in the given irreducible representation, which survives arbitrary finite direct products
  lst-quasisimple-classical-character-ratio-bound: that is the imported character-ratio bound for one quasisimple classical group; this is the closure of the gapped class under products and quotients, with that bound as one input
---

**ESTABLISHED (lane sk-trace-template, 2026-09-13, unreviewed).** Proof: `constituent-gapped-finite-groups-closed-under-products-proof`.

**Definition.** Fix `θ < 1`. `𝒢_θ` is the class of finite groups `Q` such that every irreducible complex representation `σ` of
`Q` satisfies `|χ̃_σ(q)| ≤ θ` whenever `σ(q)` is not a scalar, where `χ̃_σ = χ_σ/χ_σ(1)`.

**Theorem.**
- (a) `𝒢_θ` is closed under finite direct products, with any number of factors, and under quotients by arbitrary normal
  subgroups.
- (b) Every finite abelian group lies in `𝒢_θ` for every `θ`.
- (c) Every finite quasisimple classical group lies in `𝒢_θ` with `θ = 2^{−1/481}`
  (`lst-quasisimple-classical-character-ratio-bound`).
- (d) A groupwise θ-gapped group, in the sense of `fp-simple-groups-have-no-gapped-finite-unitary-models`, lies in `𝒢_θ`. The
  converse fails. For nonabelian `B`, the irreducible representation `σ ⊗ 1` of `A × B` sends the noncentral element `(1,b)`
  to `I`, so products of quasisimple groups are never groupwise gapped, yet by (a) and (c) they lie in `𝒢_{2^{−1/481}}`.
- (e) `𝒢_θ` is not closed under subgroups. Even permutation matrices embed `A_m` in `SL_m(F_q)`. In the standard
  `(m−1)`-dimensional representation of `A_m` (`m ≥ 4`), a 3-cycle is non-scalar with ratio `(m−4)/(m−1)`, which exceeds any
  `θ < 1` for large `m`.

**Use.** With `fp-simple-models-concentrate-on-template-constituents` (Corollary 2), no finitely presented infinite simple
group has a finite-group hyperlinear model through targets in `𝒢_θ`. See
`fp-simple-groups-have-no-models-through-classical-products`.
