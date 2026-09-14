# Products with factors in the LEF permanence closure

Lane `w3-products`, 2026-09-12. Supports `finitary-split-structures-pass-to-direct-products`,
`products-with-lef-permanence-closure-factors-are-surjunctive`, and the Attempts of
`finite-direct-products-of-surjunctive-groups-are-surjunctive`.

Conventions as in `surjunctivity-closure-properties-2026-09-12.md`, Section 0. Inputs used:
- **(B)** `products-with-lef-factors-preserve-surjunctivity`, in its general form: `G x K` is surjunctive
  whenever every finite subset of `K` embeds as a partial multiplication table into some `L` with `G x L`
  surjunctive.
- **(T)** Corollary 1 of `strict-pairs-transfer-to-table-realizations`.
- **(H)** `surjunctivity-passes-to-subgroups`.
- **(F0)** `finitary-split-extension-surjunctivity-permanence` (Theorem 0).
- **(GF)** `graph-folds-over-surjunctive-groups-are-surjunctive`.

## 1. Finitary structures pass to products

**Lemma 1.** Let `W_i = N_i ⋊ G_i` (i = 1, 2) carry finitary structures `(X_i, p^i, iota^i)` in the sense of
(F0). Put `W = W_1 x W_2 = (N_1 x N_2) ⋊ (G_1 x G_2)`, with `(g_1,g_2)` acting coordinatewise, and let
`X = X_1 ⊔ X_2`, where `G_1 x G_2` acts on `X_1` through `g_1` and on `X_2` through `g_2`. For finite
`S = S_1 ⊔ S_2` put

```text
N_S = N_1,S_1 x N_2,S_2,   p_S = p^1_S_1 x p^2_S_2,   iota_(U,S) = iota^1 x iota^2 .
```

Then `(X, p, iota)` is a finitary structure on `W` with base `G_1 x G_2`.

*Proof.*
- **(D), (D').** A product of epimorphisms onto residually finite groups is an epimorphism onto a
  residually finite group, and `N_∅ = 1 x 1`. Products of compatible embeddings are compatible embeddings.
- **(A1).** Let `n_1, ..., n_k` in `N_1 x N_2` be nontrivial, `n_j = (a_j, b_j)`. Apply (A1) of the first
  structure to the nontrivial `a_j` (take `S_1 = ∅` if there are none) and of the second to the nontrivial
  `b_j`. With `S = S_1 ⊔ S_2`, every `p_S(n_j) = (p^1(a_j), p^2(b_j))` has a nontrivial coordinate.
- **(A2).** Put `L(a,b) = L_1(a) ⊔ L_2(b)`. For `g = (g_1,g_2)` and `U ⊆ S`, the set `gL(a,b)` misses
  `S∖U = (S_1∖U_1) ⊔ (S_2∖U_2)` iff `g_1 L_1(a)` misses `S_1∖U_1` and `g_2 L_2(b)` misses `S_2∖U_2`. Then
  both coordinates satisfy their own (A2), which is the identity for `p_S`.
- **(A3).** The pointwise stabilizer of `S` in `G_1 x G_2` is `(G_1)_S_1 x (G_2)_S_2`, and invariance holds
  coordinatewise. QED

**Special case.** Every group `G` carries the trivial finitary structure `N = 1`, `X = ∅`. So for any
finitary `K = N ⋊ B`, the product `G x K = N ⋊ (G x B)` is finitary over `G x B`, with `G` acting trivially
on the sites. By (F0), `G x K` is surjunctive iff `G x B` is.

## 2. Theorem B-prime

Fix a surjunctive group `G` and put `P(G) = { K : G x K is surjunctive }`. Note `P(1)` is exactly the class
of surjunctive groups.

**Theorem B′.**
- **(a)** Every LEF group lies in `P(G)`.
- **(b)** `P(G)` is closed under subgroups.
- **(c)** If every finite subset of `K` embeds as a partial multiplication table into some member of
  `P(G)`, then `K` lies in `P(G)`. In particular `P(G)` is closed under directed unions.
- **(d)** If `K = N ⋊ B` carries a finitary structure and `B` lies in `P(G)`, then `K` lies in `P(G)`.
- **(e)** Let `Q` be the fundamental group of a connected graph of groups with injective edge maps. If some
  homomorphism `f: Q -> K` with `K` in `P(G)` is injective on every vertex group, then `Q` lies in `P(G)`.

*Proof.*
- **(a)** is (B) with `L` finite.
- **(b)** `G x K'` is a subgroup of `G x K`; apply (H).
- **(c)** is the general form of (B).
- **(d)** is the special case of Lemma 1 with (F0).
- **(e)** Let `Q` have vertex groups `Q_v`, edge groups `Q_e` and edge maps `iota_e`. Form the graph of groups
  with vertex groups `G x Q_v`, edge groups `G x Q_e` and edge maps `id x iota_e`, which are injective. Call
  its fundamental group `E`.
  - **Centrality.** The copies of `G` in the vertex groups are identified along tree edges, and each stable
    letter `t_e` satisfies `t_e (g,c) t_e^-1 = (g, iota'_e(c))`, so it commutes with `G`. So `G x 1` is
    central in `E`, and `E/(G x 1) = Q`.
  - **Retraction.** Projecting every vertex group onto `G` and sending stable letters to 1 respects all
    relations, so it gives a retraction `r: E -> G` that is the identity on `G x 1`.
  - **Splitting.** A central subgroup with a retraction splits off: `e -> (r(e), e(G x 1))` is an
    isomorphism `E ≅ G x Q`.
  - **Fold.** The map `id x f: G x Q -> G x K` is injective on every vertex group `G x Q_v`, and `G x K` is
    surjunctive. By (GF), `G x Q` is surjunctive. QED

**Corollary 1 (the closure).** Let `Cl(LEF)` be the smallest class containing the LEF groups and closed
under operations (b)–(e), with (d) and (e) taken over bases and targets inside the class. Then
`Cl(LEF) ⊆ P(G)` for every surjunctive `G`.

**Corollary 2 (products inside the closure).** `Cl(LEF)` ⊆ `P(1)`, so its members are surjunctive, and it is
closed under finite direct products: for `K_1, K_2` in `Cl(LEF)`, `K_1` is surjunctive, so `K_2` lies in
`P(K_1)` by Corollary 1.

**Instances.**
- **Kun–Thom wreaths** `W = (Z/2) wr_(G/Gamma) G` over the residually finite base `G`: finitary by instance
  (I1) of (F0), with base in LEF. So `G' x W` is surjunctive for EVERY surjunctive `G'`.
- **Kun–Thom doubles** `D = G *_Gamma G`: finitary with free kernel by instance (I2), base residually finite.
  So `G' x D` is surjunctive for every surjunctive `G'`, and `D x D` is surjunctive. That is the "first open
  test instance" named on the product claim, which is therefore covered.
- **Products of two permutational wreaths** were already covered, by Remark (B) of the closure artifact.

## 3. Where fibre-plus-compactness dies

View an injective automaton `tau` over `G x H` with alphabet `A` as an automaton over `G` with the compact
alphabet `C = A^H`. Its local rule `Phi: C^(M_G) -> C` is continuous and `H`-equivariant. For a finite
window `E ⊆ H`, `Phi` restricts to a map `C_(E M_H)^(M_G) -> C_E`, which is a self-map of `(A^E)^G` only
when `E M_H ⊆ E`. For infinite `<M_H>` no finite `E` qualifies, so G's surjunctivity never sees a finite
alphabet directly.

The device can be closed exactly when the finitely many forward coincidences of the strict certificate in
the `H`-coordinate are realized EXACTLY by total maps on a finite set, with the Garden-of-Eden window kept
injective. Permutation realizations of that kind are local embeddings into finite groups: that is LEF, and
it is Theorem B. Sofic approximations realize the coincidences only on a fraction `1 - eps` of the points.
There the decoder identity fails on a positive fraction, and repairing it is a Gromov–Weiss count in the
`H`-direction over the infinite `G`-direction alphabet, which has no finite count. So fibre-plus-compactness
reaches Theorem B′ and no further. In particular it does not give `G x H` for `H` sofic outside `Cl(LEF)`.

## 4. What stays open

- **The product claim itself** needs both factors outside `Cl(LEF)`. By
  `sofic-permanence-closure-omits-simple-fa-nonsofic-groups`, every group containing a finitely presented
  simple nonsofic FA subgroup lies outside it, for example `R^x` and the tester `U`. So the open case sits
  at the same simple Kazhdan hosts as Gottschalk's hard case.
- **A failing product** would be a Gottschalk counterexample whose strict certificate needs both
  coordinates, with neither factor in `Cl(LEF)`.
