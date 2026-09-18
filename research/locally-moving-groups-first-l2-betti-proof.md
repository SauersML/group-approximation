---
rg: 2
id: locally-moving-groups-first-l2-betti-proof
kind: route
title: Any subgroup containing a rigid stabilizer and closed under infinite-intersection conjugates is everything; untwist cocycles from G_U, or from a product of two rigid stabilizers
target: locally-moving-groups-have-vanishing-first-l2-betti-number
requires:
  - l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup
---

Notation as in the target. Open sets in `X` are infinite, and every nonempty open set contains two disjoint
nonempty open subsets (Hausdorff, no isolated points). So (LM1) makes every `G_U`, `U ≠ ∅`, infinite: it
contains the internal direct product of the nontrivial groups `G_(U_1)` and `G_(U_2)`, for disjoint
`U_1, U_2 ⊆ U`.

**Lemma (absorption).** Let `U` be nonempty open, and `K ≤ G` a subgroup with `G_U ≤ K`. Suppose every `g ∈ G`
with `gKg^(-1) ∩ K` infinite lies in `K`. Then `K = G`.

*Proof.*
- (a) Let `V` be open with `U ⊄ V`, and `g ∈ G_V`. Take `x ∈ U ∖ V`, so `g(x) = x`, and `U ∩ gU` is an open
  neighbourhood of `x`. Then `G_(U ∩ gU) ⊆ G_U ∩ G_(gU) = G_U ∩ g G_U g^(-1) ⊆ K ∩ gKg^(-1)`. This is infinite
  by (LM1), so `g ∈ K`. Hence `G_V ⊆ K` whenever `U ⊄ V`.
- (b) Let `V` be open with `W = int(X ∖ V) ≠ ∅`. Pick `u ∈ U`, and let `U_2 = W ∖ {u}`. It is nonempty and
  open, and `U ⊄ U_2`, so `G_(U_2) ⊆ K` by (a).
- Now `U_2 ∩ V = ∅`, so `U_2 ⊄ V`. Applying (a) with `U_2` in place of `U` gives `G_V ⊆ K`.
- By (LM2), `K = G`. ∎

**Case A: `G_U` nonamenable for every nonempty open `U` (item 2).** Let `c : G → ℓ^2 G` be a 1-cocycle,
`c(gh) = c(g) + g c(h)`. Choose disjoint nonempty open `U, W`, and put `A = G_U` and `B = G_W`. These commute
and meet trivially, `A` is infinite and `B` is nonamenable.
- *Spectral gap.* `ℓ^2 G` restricted to `B` is a multiple of `ℓ^2 B`. So there are a finite `S ⊆ B` and
  `ε > 0` with `Σ_(s∈S) ‖sξ − ξ‖^2 >= ε ‖ξ‖^2` for all `ξ ∈ ℓ^2 G`. Hence `Q = Σ_(s∈S) (1 − s)^*(1 − s) >= ε`
  is invertible, and `Q` commutes with `A`.
- *Untwisting on A.* For `a ∈ A` and `b ∈ B`, `c(ab) = c(ba)` gives `(1 − b) c(a) = (1 − a) c(b)`. So
  `Q c(a) = (1 − a) ζ` with `ζ = Σ_s (1 − s)^* c(s)`, and `c(a) = (1 − a) η` with `η = Q^(-1) ζ`.
- Put `c' = c + ∂η`, where `∂η(g) = gη − η`. Then `c'` vanishes on `A`.
- `K = {g : c'(g) = 0}` is a subgroup, containing `G_U = A`.
- If `gKg^(-1) ∩ K` is infinite, then every `k` in it has `g^(-1) k g ∈ K`. So
  `k c'(g) = c'(kg) = c'(g · g^(-1)kg) = c'(g)`. A vector of `ℓ^2 G` invariant under an infinite subgroup is
  `0`, so `c'(g) = 0` and `g ∈ K`.
- By the absorption lemma, `K = G`. So `c = −∂η` is inner, and `H^1(G, ℓ^2 G) = 0`.
- By Peterson–Thom (arXiv:0708.4327, Theorem `cohom`, source l.302–305: `β_1^(2)(G) = dim_(LG) H^1(G, ℓ^2 G)`),
  `β_1^(2)(G) = 0`.

**Case B: some `G_U` amenable (item 1 in the remaining case).**
- `G_U` is wq-normal in `G`, by Peterson–Thom's Lemma `alter` (source l.744–747): `H` is wq-normal iff every
  intermediate `H ⊆ K ⊊ G` has some `g ∉ K` with `gKg^(-1) ∩ K` infinite. The absorption lemma says exactly
  that no such `K` exists.
- `G_U` is infinite and amenable, so `β_1^(2)(G_U) = 0`: it is its own infinite normal amenable subgroup
  (`l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup`).
- Peterson–Thom Theorem `main1` (source l.788–791: for an infinite wq-normal `H`, `β_1^(2)(H) >= β_1^(2)(G)`)
  gives `β_1^(2)(G) = 0`.

Cases A and B are exhaustive, so item 1 holds. Item 3 is proved in the target.
