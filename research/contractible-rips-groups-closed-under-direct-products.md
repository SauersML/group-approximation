---
rg: 2
id: contractible-rips-groups-closed-under-direct-products
kind: claim
title: Rips complexes of a direct product for the l-infinity generating set are products up to homotopy, so contractibility passes to products
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for Z^n with the standard (l^1) generators; this is a product formula for Rips complexes of arbitrary direct products with the l^infinity generating set
  group-rips-complexes-are-cayley-graph-flag-complexes: that identifies one group's Rips complexes with clique complexes of its Cayley graphs; this computes Rips complexes of a direct product from those of its factors
---

Let `(G,S)` and `(H,T)` be finitely generated groups with finite symmetric
generating sets not containing `1`, and put
`S ⊠ T = ((S ∪ {1}) × (T ∪ {1})) ∖ {(1,1)}`, a finite symmetric generating set of
`G × H`. Then:

1. `d_{S⊠T}((g,h),(g',h')) = max(d_S(g,g'), d_T(h,h'))`;
2. for every `r ≥ 0`, `R_r(G×H, S⊠T)` is the categorical product
   `R_r(G,S) ⊓ R_r(H,T)`: a finite subset is a simplex iff both its
   projections are simplices;
3. `|R_r(G×H, S⊠T)| ≃ |R_r(G,S)| × |R_r(H,T)|`.

Consequences:

- if `R_r(G,S)` and `R_r(H,T)` are contractible, so is `R_r(G×H, S⊠T)`;
- if `(G,S)` and `(H,T)` are of type `ℝ` in the sense of Li–Sánchez Saldaña
  (arXiv:2608.24279: contractible for all `r ≥ r_0`), so is `(G×H, S⊠T)`;
- if `G` and `H` each have some contractible Rips complex, at possibly different
  generating sets and scales, so does `G × H`. Rescale both to scale 1 by item 1
  of `group-rips-complexes-are-cayley-graph-flag-complexes`:
  `R_r(G,S) = R_1(G, B_S(r) ∖ {1})`.

Model test: `G = H = Z`, `S = T = {±1}`, `r = 1`. `S ⊠ T` is the king-move
generating set of `Z^2`, `R_1` is the flag complex of the king graph, and it is
homotopy equivalent to a line times a line, a point. Its vertex-link counts
`1, 8, 12, 4` give `χ = 1 − 8/2 + 12/3 − 4/4 = 0 = χ(Z^2)`.

Credit: Li–Sánchez Saldaña prove `Z^n × F` with `F` finite is of type `ℝ` for the
generating set `S ∪ T` (their Theorem 1.6) and do not state a general product
theorem. A product formula for Vietoris–Rips complexes of `l^∞` products of
metric spaces may be known in applied topology. We did not locate one: the check
was bounded, and `arXiv:1706.04876` (Adamaszek–Adams–Frick), checked, is not it.

Proof: `contractible-rips-groups-closed-under-direct-products-proof`.
