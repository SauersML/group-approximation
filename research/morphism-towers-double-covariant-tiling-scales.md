---
rg: 2
id: morphism-towers-double-covariant-tiling-scales
kind: claim
title: A 2-dimensional morphism between SFT languages with all letter images of both sides at least 2 turns a covariant tiling family at scale D into one at scale 2D over the same field, on an operator Kakutani–Rokhlin tower
distinct_from:
  constant-shape-substitutions-inflate-torus-tiling-modules: that inflates torus modules and needs one constant shape; this inflates covariant families (with translation operators) and allows letter-dependent shapes, where the inflated torus is undefined
  matricial-z2-sft-crossed-products-give-quantum-tilings: that equates matriciality with covariant families at every scale; this produces families at scale 2D from one at scale D when a shape-consistent morphism exists
  torus-tiling-modules-restrict-to-smaller-scales: that moves torus modules down in scale on one torus; this moves covariant families up in scale on a larger space
artifacts:
  - research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md
---

**ESTABLISHED (unreviewed).** Let `Ω_S ⊆ S^(Z^2)` and `Ω_T ⊆ T^(Z^2)` be SFTs, `k` a field, and
`ω : L(Ω_S) -> T^(*2)` a 2-dimensional morphism in Labbé's sense (whenever `u`, `v` and `u ⊙^i v` are legal, `ω(u) ⊙^i ω(v)`
is well defined and equals `ω(u ⊙^i v)`). Assume:
- (H1) `ω(L(Ω_S)) ⊆ L(Ω_T)`;
- (H2) every letter image `ω(a)` has width `w(a) >= 2` and height `h(a) >= 2`.

Let `(W', E'_a(z), u_1, u_2)` be a nonzero finite-dimensional covariant `D'`-family for `Ω_S` over `k`, with `D' >= 1`
(relations (Q1)–(Q3) as in `torus-quantum-tilings-decide-matriciality-of-sft-rings`, artifact §1). Then there is a
nonzero finite-dimensional covariant `2D'`-family for `Ω_T` over `k`, of dimension `sum_a w(a) h(a) rank E'_a(0)`.

**Construction** (artifact §2–§4).
1. **Skeleton.** The width projections `M_(=m)(z) = sum_(w(a)=m) E'_a(z)` are column-constant, and the height
   projections row-constant (Lemma 1: an illegal domino times (Q3)). So `u_2` commutes with `M(0)` and `u_1` with `N(0)`.
2. **Tower space.** `W_T = ⊕_((i,j)) M_(>i)(0) N_(>j)(0) W'`. The new translations `A_1, A_2` advance a pointer inside
   the current block, and apply `u_1^(-1)`, `u_2^(-1)` with the matching width or height projection when the pointer
   leaves it.
3. **Idempotents.** `E_b(0)` acts on summand `(i,j)` as `sum_(ω(a)_((i,j)) = b) E'_a(0)`, and
   `E_b(z) = A^z E_b(0) A^(-z)`.
4. **Evaluation formula** (Proposition 5). For `z ∈ [0,4D']^2`, `E_b(z)` is diagonal. Its entries are evaluations, on
   the commutative box algebra of `[0,2D']^2`, of the classical functions "letter of `ω(ρ)` at `(i,j) + z`".
   (Q2) and (Q3) at scale `2D'` follow, since `ω` of a legal box is legal.

Route: `morphism-towers-double-covariant-tiling-scales-proof`.
