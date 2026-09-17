---
rg: 2
id: artin-ghost-ideal-localizes-to-standard-parabolics-proof
kind: route
title: "Proof: membership in ZA(1 − s) is a condition on the coset sums along g⟨s⟩, and these cosets lie inside the cosets of A_T"
target: artin-ghost-ideal-localizes-to-standard-parabolics
requires: []
---

**Literature input.** For `T ⊆ S`, `A_T` is the Artin group of the induced subdiagram, and
`A_X ∩ A_Y = A_{X ∩ Y}` (H. van der Lek, thesis, Nijmegen 1983; L. Paris, arXiv:1211.7339,
Theorem 5.4). Every `s ∈ S` has infinite order, since the homomorphism `A → Z` sending every
generator to `1` is well defined (the defining relations are homogeneous).

**Lemma 1 (coset sums).** Let `H` be a group and `s ∈ H` of infinite order. For
`x = Σ_h a_h h ∈ ZH`, `x ∈ ZH·(1 − s)` if and only if `Σ_{k ∈ Z} a_{g s^k} = 0` for every
`g ∈ H`.

*Proof.* Right multiplication by `s` maps each left coset `g⟨s⟩` to itself, so `y` and `ys`
have the same coefficient sum on every such coset, and `y(1 − s)` has sum `0` on each.
Conversely, suppose all coset sums of `x` vanish. Fix representatives `g` of `H/⟨s⟩` and put
`b_{g s^k} = Σ_{j ≤ k} a_{g s^j}`. On each coset, `b` vanishes for `k` below the support of
`x` and, because the total sum is `0`, for `k` above it; only finitely many cosets meet the
support of `x`. So `y = Σ b_h h ∈ ZH`. The coefficient of `g s^k` in `ys` is `b_{g s^{k−1}}`,
so the coefficient of `g s^k` in `y(1 − s)` is `b_{g s^k} − b_{g s^{k−1}} = a_{g s^k}`.
Hence `x = y(1 − s)`. ∎

**Expansion.** `A` is the disjoint union of the cosets `rA_T` (`r ∈ R`), so
`ZA = ⊕_{r} r·ZA_T` as abelian groups, and the expansion `x = Σ r y_r` is unique: `r y_r` is
the restriction of `x` to `rA_T`.

**Slicing.** Let `s ∈ T`. Every left coset `g⟨s⟩` lies inside the coset `gA_T`, since
`s ∈ A_T`. Write `g = r h` with `r ∈ R`, `h ∈ A_T`. The restriction of `x` to `g⟨s⟩ = r·h⟨s⟩`
is `r` times the restriction of `y_r` to `h⟨s⟩ ⊆ A_T`, so the coset sum of `x` on `g⟨s⟩` equals
the coset sum of `y_r` on `h⟨s⟩`. As `(r, h⟨s⟩)` runs over `R × A_T/⟨s⟩`, `g⟨s⟩` runs over
`A/⟨s⟩`. By Lemma 1 applied in `H = A` and in `H = A_T` (where `s` still has infinite order),
`x ∈ ZA(1 − s)` iff every `y_r ∈ ZA_T(1 − s)`. ∎

**Consequences.** Intersecting over `s ∈ T` gives
`⋂_{s∈T} ZA(1 − s) = ⊕_r r·G(A_T)`. Since `G(A)` is contained in the left-hand side, it is
contained in `⊕_r r·G(A_T)`, and it is `0` when `G(A_T) = 0`.

**Free rank-two case.** If `S = {s, t}` with `m_st = ∞`, then `A` is free on `s, t`. Let `Y` be
the graph with vertex set `A/⟨s⟩ ⊔ A/⟨t⟩` and one edge `g` joining `g⟨s⟩` to `g⟨t⟩` for each
`g ∈ A`. This is the Bass–Serre tree of `A = ⟨s⟩ * ⟨t⟩`. By Lemma 1, `x = Σ a_g g ∈ G(A)` iff
the 1-chain `Σ a_g g` on `Y` has zero boundary. A tree has no nonzero 1-cycles (a finite
subforest has a vertex of degree 1, where the boundary coefficient is the single edge
coefficient). So `G(A) = 0`. With the theorem, `G(A_Λ) = 0` whenever `Λ` has an edge labelled
`∞`. ∎
