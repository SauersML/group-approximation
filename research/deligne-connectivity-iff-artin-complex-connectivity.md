---
rg: 2
id: deligne-connectivity-iff-artin-complex-connectivity
kind: claim
title: "Every Artin group has k-connected Deligne complex iff every Artin group with infinite Coxeter group has k-connected Artin complex"
---

For an Artin group `A = A_Γ` on a finite set `S`, let `Φ(A)` be the modified Deligne
complex of Charney and Davis: the geometric realization of the poset of cosets `gA_U`
(`g ∈ A`, `U ⊆ S` with `W_U` finite), ordered by inclusion. Let `Δ(A)` be the Artin
complex of `artin-complex-top-homology-is-intersection-of-ideals`. Let
`k ∈ {0, 1, 2, …} ∪ {∞}`, where "∞-connected" means contractible.

1. **One group.** Suppose `W_Γ` is infinite and `Φ(A_{S∖R})` is `(k − |R| + 1)`-connected
   for every nonempty `R ⊆ S` with `|R| ≤ k`. Then `π_j(Φ(A)) ≅ π_j(Δ(A))` for every
   `j ≤ k`. So `Φ(A)` is `k`-connected iff `Δ(A)` is, and for `k = ∞` the two complexes
   are homotopy equivalent.
2. **All groups.** `Φ(A_Γ)` is `k`-connected for every finite Coxeter graph `Γ` iff
   `Δ(A_Γ)` is `k`-connected for every finite Coxeter graph `Γ` with `W_Γ` infinite.

When `W_Γ` is finite, `A` itself is the largest vertex of `Φ(A)`, so `Φ(A)` is a cone.

**Consequences.** Charney and Davis (J. Amer. Math. Soc. 8 (1995)) show that `Φ(A)` is
homotopy equivalent to the universal cover of the Salvetti complex. Therefore:

- `k = ∞`: the K(π,1) conjecture (`artin-group-k-pi-1-conjecture`) holds for every Artin
  group iff every Artin complex with infinite `W` is contractible. For a single group: if
  the Salvetti complex of `A` is aspherical and `W` is infinite, then so is the Salvetti
  complex of every `A_T` (L. Paris, arXiv:1211.7339, Theorem 5.5), every `Φ(A_T)` is
  contractible, and `Δ(A)` is contractible. So the ideal `⋂_s ZA·(1 − s)` vanishes. This
  is unconditional when every subset of `S` generating a finite Coxeter group has at most
  two elements (Charney–Davis 1995, dimension-2 case).
- `k = 2`: the K(π,1) conjecturette `π_2(Sal(A)) = 0` holds for every Artin group iff
  `H_2(Δ(A)) = 0` for every Artin group with infinite `W` and `|S| ≥ 3`. These complexes
  are simply connected (below), so Hurewicz applies. For `|S| = 3` this `H_2` is the
  ideal `⋂_s ZA·(1 − s)`.
- `k = 1`: every Artin complex with infinite `W` is simply connected. For `|S| = 2` it is
  the Bass–Serre tree of the free group. For `|S| ≥ 3`, `A` is the colimit of its maximal
  standard parabolic subgroups along their pairwise intersections, because every defining
  relation involves only two generators; by Tits' criterion for coset complexes
  (H. Abels and S. Holz, *Higher generation by subgroups*, J. Algebra 160 (1993)) the
  complex is simply connected. Item 2 then reproves, without the Charney–Davis equivalence,
  that `Φ(A)` is simply connected for every Artin group.

This answers how much connectivity of these complexes is known in general: simple
connectivity only. The next step, `k = 2`, is equivalent to the open conjecturette. Any
general theorem on Artin complexes transfers to Deligne complexes and conversely. Proof
route: `deligne-connectivity-iff-artin-complex-connectivity-proof`.
