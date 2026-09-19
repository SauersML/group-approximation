---
rg: 2
id: nv-brick-groupoid-and-kazhdan-host-are-both-o2-proof
kind: route
title: "Factor both groupoid algebras as (something unital, separable, simple, nuclear) tensor O_2 and apply Kirchberg's O_2-absorption theorem"
target: nv-brick-groupoid-and-kazhdan-host-are-both-o2
requires:
  - amenable-purely-infinite-groupoid-full-group-hosts-kazhdan
  - rs-boundary-groupoid-is-expansive-amenable-kazhdan-host
  - matui-groupoid-homology-kunneth-and-full-shift-vanishing
  - kazhdan-host-crossed-product-is-simple-and-nuclear
---

*Demoted 2026-09-18 (referee pass). Lens 2 refuted Step 5: the Rordam-Sierakowski
sentence quoted there is an **existence** statement ("`G` admits a free, amenable,
minimal action ... such that `C(X) x|_r G` is a Kirchberg algebra"), and it was applied
universally to the host's specific `M`, which is not that action but the one built in
Steps 1-3 of `amenable-purely-infinite-groupoid-kazhdan-host-proof`. The four properties
Step 5 actually needs (unital, separable, simple, nuclear) are now the open prerequisite
`kazhdan-host-crossed-product-is-simple-and-nuclear`, so this route derives OPEN. Steps
1-4 and 6-8 were checked by all three lenses and stand; the text below is unchanged and
kept as the attempt.*

All groupoids below are second countable, locally compact, Hausdorff and étale with
compact unit space, so their reduced C*-algebras are unital and separable.

## Step 1 (self-contained): the reduced algebra of a product groupoid is the minimal
tensor product

Let `𝒢`, `ℋ` be second countable locally compact Hausdorff étale groupoids. For a unit
`x` write `λ_x` for the regular representation of `C_c(𝒢)` on `ℓ²(𝒢_x)`, where
`𝒢_x = s^{-1}(x)`; by definition `‖a‖_r = sup_x ‖λ_x(a)‖`, and `⊕_x λ_x` is a faithful
representation of `C*_r(𝒢)`.

1. The product groupoid `𝒢 × ℋ` is again second countable locally compact Hausdorff
   étale, and `(𝒢 × ℋ)_{(x,y)} = 𝒢_x × ℋ_y`, so
   `ℓ²((𝒢 × ℋ)_{(x,y)}) = ℓ²(𝒢_x) ⊗ ℓ²(ℋ_y)` canonically.
2. The map `f ⊗ g ↦ ((γ, η) ↦ f(γ)g(η))` identifies `C_c(𝒢) ⊙ C_c(ℋ)` with a dense
   *-subalgebra of `C_c(𝒢 × ℋ)` (dense for the inductive limit topology, by
   Stone–Weierstrass on each compact open bisection of the product, whose basis consists
   of products of bisections); the convolution and involution of `𝒢 × ℋ` restrict to the
   tensor-product operations, because a factorization `(γ,η) = (γ_1,η_1)(γ_2,η_2)` is a
   pair of factorizations.
3. Under the identification of item 1, `λ_{(x,y)} = λ_x ⊗ λ_y` on `C_c(𝒢) ⊙ C_c(ℋ)`.
   Hence `⊕_{(x,y)} λ_{(x,y)} = (⊕_x λ_x) ⊗ (⊕_y λ_y)` is the tensor product of two
   faithful representations, whose norm on the algebraic tensor product is the minimal
   tensor norm (independence of the minimal norm from the choice of faithful
   representations). By item 2 that same norm is the reduced norm of `𝒢 × ℋ` restricted
   to the dense subalgebra.

So `C*_r(𝒢 × ℋ) ≅ C*_r(𝒢) ⊗_min C*_r(ℋ)`. All algebras occurring below are nuclear, so
`⊗_min = ⊗_max = ⊗` and no ambiguity remains.

## Step 2 (import): `C*_r(G_2) ≅ O_2`

`G_2` is the Deaconu–Renault groupoid of the one-sided full shift on two letters, i.e.
the Cuntz groupoid; its reduced (= full, the groupoid being amenable) C*-algebra is the
Cuntz algebra `O_2`. Standard; see J. Renault, *A groupoid approach to C\*-algebras*,
LNM 793, III.2, and Kumjian–Pask–Raeburn–Renault, *Graphs, groupoids, and Cuntz–Krieger
algebras*, J. Funct. Anal. 144 (1997). The graph records the same identification in
`matui-sft-groupoid-homology-is-k-theory` ("`H_0 = K_0` and `H_1 = K_1` of its
Cuntz–Krieger algebra"). `O_2` is unital, separable, simple and nuclear.

## Step 3 (import): Kirchberg's O_2-absorption theorem

> "The Kirchberg `𝒪_2`-absorption theorem ([14], [15]) states that the Cuntz algebra
> `𝒪_2` tensorially absorbs all unital simple separable nuclear C\*-algebras `A`;
> `A ⊗ 𝒪_2 ≅ 𝒪_2`."

Y. Suzuki, *Equivariant `O_2`-absorption theorem for exact groups*, arXiv:2004.09461,
Introduction (fetched 2026-09-18), quoting [14] E. Kirchberg, *The classification of
purely infinite C\*-algebras using Kasparov's theory*, and [15] E. Kirchberg and
N. C. Phillips, *Embedding of exact C\*-algebras in the Cuntz algebra `O_2`*, J. reine
angew. Math. 525 (2000), 17–53. This is the same import the graph already uses in
`stw99-xvi-reference-targets-proof` ("`D ⊗ O_2 ≅ O_2` holds for every unital simple
separable nuclear `D` (Kirchberg's `O_2`-absorption theorem)"). **No UCT is used**, so
the open claim `trivial-k-theory-kirchberg-algebras-are-o2` is not invoked anywhere here.

## Step 4: `C*_r(G_2^n) ≅ O_2`

By Steps 1 and 2, `C*_r(G_2^n) ≅ O_2^{⊗n}`. Induction: `O_2^{⊗1} = O_2`; if
`O_2^{⊗(n-1)} ≅ O_2`, then `O_2^{⊗n} ≅ O_2 ⊗ O_2 ≅ O_2` by Step 3 with `A = O_2`
(unital, separable, simple, nuclear).

## Step 5: `C*_r(𝒢_W1) ≅ O_2`

`𝒢_W1 = (M ⋊ Γ) × G_2`, and `C*_r(M ⋊ Γ) = C(M) ⋊_r Γ`. By
`amenable-purely-infinite-groupoid-full-group-hosts-kazhdan` the action `Γ ↷ M` is free,
minimal and topologically amenable, and that node quotes Rørdam–Sierakowski verbatim
(arXiv:1006.1304v3, source tex l.1443–1449): "Let $G$ be a countable discrete group. Then
$G$ admits a free, amenable, minimal action on the Cantor set $X$ such that
$C(X) \rtimes_r G$ is a Kirchberg algebra […] in the UCT class if and only if $G$ is
exact and non-amenable." `Γ = Z^3 ⋊ SL_3(Z)` is exact (it is linear over `Z`; the graph's
`commutative-ring-linear-groups-have-property-a` is used for exactness in the host route)
and non-amenable, so `A := C(M) ⋊_r Γ` is a unital separable **Kirchberg** algebra: in
particular unital, separable, simple and nuclear. By Step 1,
`C*_r(𝒢_W1) ≅ A ⊗ O_2`, and by Step 3 this is `O_2`.

Only "unital separable simple nuclear" is used, not pure infiniteness, and not the UCT.

## Step 6: `C*_r(𝒢_RS) ≅ O_2`

`rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` item 4 states that
`C(Ω) ⋊ Γ' = C(Ω) ⋊_r Γ'` is simple, nuclear and purely infinite; `Ω` is a Cantor set and
`Γ'` is countable, so the algebra is unital and separable. Step 3 and Step 1 give
`C*_r(𝒢_RS) = (C(Ω) ⋊_r Γ') ⊗ O_2 ≅ O_2`.

## Step 7: homology

`matui-groupoid-homology-kunneth-and-full-shift-vanishing` is ESTABLISHED and states,
with the consequence derived there: `H_*(G_2) = 0`, and `H_*(𝒢 × G_2) = 0` for **every**
étale groupoid `𝒢`. Applying it with `𝒢 = G_2^{n-1}`, with `𝒢 = M ⋊ Γ` and with
`𝒢 = Γ' ⋉ Ω` gives item 2 of the target.

## Step 8: the listed invariants

`K_*(O_2) = 0`; `O_2` is simple, so its ideal lattice is `{0, O_2}`; it is purely
infinite, so it has no tracial (indeed no quasitracial) state and its Cuntz semigroup is
`{0, ∞}`; `dim_nuc(O_2) = 1` (Winter–Zacharias). These are properties of one algebra, so
they hold identically for the three groupoids by items 1.

## Step 9: the class kill and the Cartan gate

Let `P` be any property of ample groupoids that depends only on the isomorphism class of
`C*_r(𝒢)` and of `H_*(𝒢)`. By items 1–2, `P(G_2^n) ⟺ P(𝒢_W1)`. If the implication
"`P(𝒢)` ⟹ `[[𝒢]]` is Haagerup" (or "⟹ every Kazhdan subgroup of `[[𝒢]]` is finite") held
for all ample `𝒢`, it would apply to `𝒢_W1`, whose full group contains the infinite
Kazhdan group `Γ`; a proper conditionally negative definite function on `[[𝒢_W1]]`
restricts to a proper one on `Γ`, contradicting Delorme–Guichardet (BdlHV Theorem 2.12.4)
as in the host node. So no such `P` exists.

For the gate, both `G_2^n` and `𝒢_W1` are ample, Hausdorff, second countable, minimal and
effective (`G_2` is minimal and effective and products preserve both, as recorded in
`product-two-graph-kp-elementary-simple-kazhdan-not-mf-proof`; `𝒢_W1` is minimal and
effective by items 2–3 of the host node). `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids`
then says that a diagonal-preserving isomorphism of the algebras forces the groupoids to
be isomorphic, and the converse is immediate. Finally `[[·]]` is a groupoid invariant, so
`G_2^n ≅ 𝒢_W1` would give `Γ ≤ nV`, which contradicts the Haagerup property of `nV`. This
is the necessary prerequisite recorded in the target.
