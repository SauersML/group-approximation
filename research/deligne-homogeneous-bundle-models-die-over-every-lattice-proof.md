---
rg: 2
id: deligne-homogeneous-bundle-models-die-over-every-lattice-proof
kind: route
title: Discharge the congruence-subgroup hypothesis of the lattice-residual kill by reading off type C_2 and real rank two from the Margulis datum and importing Rapinchuk's centrality theorem
target: deligne-homogeneous-bundle-models-die-over-every-lattice
requires: [deligne-homogeneous-bundle-models-die-at-lattice-residual, sp4-forms-have-central-congruence-kernel]
---

The notation is that of the target.

## Imported, verbatim

- From `deligne-homogeneous-bundle-models-die-at-lattice-residual` (ESTABLISHED), Statement:
  - "(H1) The parameter is of order 3 or 6. `t'` lies in `{1/3, 2/3, 1/6, 5/6}`."
  - "(H2) Splitting forces residual finiteness. Let `n in {3, 6}` be the order of `t'`. Then there is a
    homomorphism `f : Lambda_0~ -> T` with `f(z) = -t'`. The map `(p, f)` embeds `Lambda_(0,n)` into
    `Lambda_0 x T`, so `Lambda_(0,n)` is residually finite."
  - "(b) *Under CSP.* By Margulis arithmeticity, `Lambda_(0,n)` is an arithmetic lattice in `G_n` with an
    associated absolutely almost simple, simply connected group `H` over a totally real field. If `H` has the
    congruence subgroup property, (H2) contradicts Deligne's theorem in the form of Stover's Theorem 3.3, since
    `n >= 3 > 2 >= #M(empty, H)`."
  - Also: "Only `Lambda cap T` finite is used, not discreteness of `Lambda`."
- From the same node's proof, Step 4: "By the Margulis passage (Stover p. 10), `Lambda_(0,n)` is arithmetic,
  with an associated absolutely almost simple, absolutely simply connected group `H` over a totally real field
  `k`." That passage of Stover, as quoted there, reads: "there is an absolutely almost simple, absolutely simply
  connected linear algebraic group G deﬁned over a number ﬁeld k and a surjection p from G(k ⊗ R) onto G with
  compact kernel so that the image of Γ in G is commensurable with the image of p(G(Ok))". Here the target `G`
  is the adjoint group of `G_n`, namely `PSp_4(R)`, and "Since G is real, k is a totally real number ﬁeld."
- From `sp4-forms-have-central-congruence-kernel` (ESTABLISHED by citation): "Let `k` be a number field and `H`
  an absolutely almost simple, simply connected `k`-group of absolute type `C_2` ... Suppose `H(k_v0)` has real
  rank 2 at some real place `v0` ... Then the congruence kernel `C^(V_inf)(H)` is central ... In other words,
  `H` has the congruence subgroup property in the sense of Stover".

**Standard facts** (no citation node).
- For a totally real `k`, `H(k (x) R) = prod over real places v of H(k_v)`.
- An absolutely almost simple `k`-group stays absolutely almost simple over each `k_v`, so each `H(k_v)` has
  simple real Lie algebra `h_v` with `h_v (x) C = Lie(H)(C)`.
- A surjective Lie group homomorphism has surjective differential. The Lie algebra of a compact group is
  compact.
- `sp_4(R)` is simple and noncompact, with complexification `sp_4(C)`, of type `C_2`, and real rank 2.

## Step 1. The Margulis datum has type C_2 and real rank 2 at one place

Let `Lambda_0` be a lattice of `Sp_4(R)`, suppose a homogeneous model exists over it, and let `n in {3, 6}` be as
in (H1). Take `H`, `k` and `p : H(k (x) R) -> PSp_4(R)` as in the imported Margulis passage for
`Lambda_(0,n) <= G_n`.

- `dp : sum_v h_v -> sp_4(R)` is surjective, and its kernel is the Lie algebra of the compact group `ker p`, so
  it is a compact ideal.
- The ideals of `sum_v h_v` are sums of some of the simple summands `h_v`. So `ker dp` is the sum of the `h_v`
  for `v` outside a set `A` of places.
- `dp` maps `sum over v in A of h_v` isomorphically onto the simple algebra `sp_4(R)`. So `A` is a single place
  `v0`, and `h_v0 = sp_4(R)`.
- Complexifying, `Lie(H)(C) = sp_4(C)`, so `H` has absolute type `C_2`, and `rank_R H(k_v0) = 2`.

## Step 2. CSP holds for H

`H` is absolutely almost simple and simply connected (imported passage), of absolute type `C_2`, with
`H(k_v0)` of real rank 2 (Step 1). By `sp4-forms-have-central-congruence-kernel`, `H` has the congruence
subgroup property in Stover's sense. No isotropy of `H` over `k` was used. This is what covers the cocompact
`Lambda_0`, where `H` is `k`-anisotropic.

## Step 3. Conclusion

The hypothesis of (H3b), "If `H` has the congruence subgroup property", holds by Step 2. So (H2) contradicts
Stover's Theorem 3.3 exactly as in (H3b).
- (H2) says `Lambda_(0,n)` is residually finite.
- Theorem 3.3 says it is not, because `G_n` covers `Sp_4(R)` with degree `n >= 3 > 2 >= #M(empty, H)`.

Hence no homogeneous model exists over `Lambda_0`. `Lambda_0` was arbitrary, which proves the Theorem. As in
the w20 node, only finiteness of `Lambda cap T` was used.

**Corollary.** This is the Theorem for cocompact `Lambda_0`, restated for the bundle `L_t/Lambda -> K`.
- A discrete `Lambda` has `Lambda cap T` finite, since `T` is compact.
- An `E_3`-action by left translation over the `Gamma`-action, with `z` rotating fibres nontrivially, is a
  homomorphism `rho~` lifting `Gamma <= Sp_4(R)` with `rho~(z) not in Lambda`, which is a homogeneous model.
- A homogeneous continuous untwisting in the sense of the (U) node is such a model over a cocompact
  `Lambda_0`. This is recorded in the w20 node's Setting.
