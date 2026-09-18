---
rg: 2
id: basilica-fp2-covers-contain-free-subgroups
kind: claim
title: Every cover of type FP_2 of the Basilica group contains a non-abelian free subgroup, so the Basilica group is not of type FP_2 and has no amenable FP_2 cover
requires:
  - fp-covers-of-grigorchuk-groups-are-large
distinct_from:
  fp-covers-of-grigorchuk-groups-are-large: that is Erschler's theorem for finitely presented covers; this extends it to covers of type FP_2 by de Cornulier's perfect-kernel argument, which Benli–Grigorchuk–de la Harpe print only for the Grigorchuk group.
---

**ESTABLISHED** (lane transfer of a printed argument, not reviewed). The argument is Yves de Cornulier's,
reproduced in Benli–Grigorchuk–de la Harpe, arXiv:1206.2072, Proposition 5.11, where it is stated and proved
for the first Grigorchuk group `𝔊`. Here it is checked for the Basilica group `𝔅` using BGdlH's own
contracting-cover machinery. No priority is claimed.

## Statement

1. If `E` is of type `FP_2` over `Z` and `E ↠ 𝔅`, then `E` maps onto one of BGdlH's approximating groups `G_n`
   and contains a non-abelian free subgroup.
2. `𝔅` is not of type `FP_2` over `Z`, because `𝔅` is amenable and contains no `F_2`.
3. No amenable group of type `FP_2` maps onto `𝔅`.

## Ingredients (BGdlH, read at source)

- **(a) Contracting cover.** Example 2.17 records the recursion `Φ(a) = (b,1)τ`, `Φ(b) = (a,1)`. It says the pair
  is faithful, contracting and self-replicating, and that the universal contracting cover is
  `G_0 = ⟨a, b | ∅⟩ ≅ F_2`.
  - The standard cover of Definition 2.8 is `G_0^un / ⟨⟨E⟩⟩`. For `𝔅` the lifts `h(x, n)` can be chosen with
    exact free-group sections: `b = (a,1)`, `a^2 = (b,b)`, `a b a^(−1) = (1,a)`, `a^(−2) b = (b^(−1)a, b^(−1))`,
    `a^(−1) b a^(−1) = (b^(−1), b^(−1)a)`, and their inverses, which cover the nucleus `{1, a^±, b^±, c^±}`,
    `c = a^(−1) b`.
  - These are computed with the product rule `(g_0,g_1)τ · (h_0,h_1)τ' = (g_0 h_(τ(0)), g_1 h_(τ(1))) ττ'`, for
    example `a^(−1) = (1, b^(−1))τ` and `a b a^(−1) = (b,a)τ · (1,b^(−1))τ = (1,a)`.
  - So `E = {1}` and the standard cover is `G_0 = F_2`.
- **(b) Approximants.** Definition 2.10 sets `G_n = G_0 / ker(φ_n)` with `φ_n : G_0 → G_0 ≀^n S_d`. Lemma 2.12
  gives `lim G_n = 𝔅` in the space of marked groups.
- **(c) Free subgroups.** Theorem 2.14: since `G_0` contains `F_2`, every `G_n` contains a non-abelian free
  subgroup.
- **(d) Covers.** Proposition 3.3: a finitely presented cover of a limit of a convergent sequence of marked groups
  is a cover of `G_n` for all large `n`.
- **(e) FP_2 groups** (BGdlH §5, item (iv), citing Brown, *Cohomology of groups*, VII.5 Exercise 3): a group is of
  type `FP_2` iff it is `F/P` with `F` finitely presented and `P` a perfect normal subgroup.

## Proof

- **`G_n` is residually soluble.** `G_n ≅ φ_n(G_0) ≤ F_2^(2^n) ⋊ W_n`, where `W_n` is the iterated wreath product
  of `n` copies of `C_2`, a finite 2-group.
  - `H_n = G_n ∩ F_2^(2^n)` is normal of finite index. It is residually soluble, since free groups are residually
    nilpotent (Magnus) and products and subgroups inherit this.
  - `G_n / H_n ≤ W_n` is soluble.
  - Given `1 ≠ h ∈ H_n`, pick `L ⊴ H_n` with `H_n / L` soluble and `h ∉ L`. The core `L_(G_n)` is a finite
    intersection of conjugates. So `H_n / L_(G_n)` is soluble, hence so is `G_n / L_(G_n)`, and `h ∉ L_(G_n)`.
    Elements outside `H_n` survive in `G_n / H_n`.
  - A perfect subgroup of a residually soluble group has trivial image in every soluble quotient, so it is trivial.
- **De Cornulier's step.** Let `E ↠ 𝔅` with `E` of type `FP_2`, and write `E = F/P` as in (e). `F` is a
  finitely presented cover of `𝔅`, so by (d) there is `K_n ⊴ F` with `F / K_n ≅ G_n`.
  - The image of `P` in `G_n` is a perfect normal subgroup, hence trivial. So `F / P K_n ≅ G_n`.
  - `F / P K_n` is a quotient of `F / P = E`. So `E ↠ G_n`, and `G_n ⊇ F_2` by (c).
  - Free groups lift along surjections, so `E ⊇ F_2`.
- Items 2 and 3 follow, because `𝔅` is amenable (Bartholdi–Virág), so it and its subgroups contain no `F_2`. ∎

## Consequences

- **Hartung's computations** (arXiv:1106.1098, Dwyer quotients `M_c(𝔅)` for `c ≤ 103`) suggest that `H_2(𝔅; Z)` is
  infinitely generated. That would also give item 2, but only conjecturally. Item 2 here is proved.
- **The Basilica HNN extension** has no ascending base of type `FP_2`, not only none that is finitely presented
  (see `basilica-hnn-has-no-finitely-presented-ascending-base`). Moreover Brown's homological criterion on its
  Bass–Serre tree fails already in degree 2, since the vertex group `𝔅` is not `FP_2`.

## Lesson for general BH

Finiteness of a branch group cannot be recovered even homologically from any cover that stays amenable. The
contracting approximants are virtually subgroups of products of free groups, so they have no perfect normal
subgroups. De Cornulier's perfect-kernel trick then turns "type `FP_2`" into "finitely presented" for free.
For BH routes this sharpens the germ-group gate: a germ or base group that needs a branch group as a quotient
cannot be `FP_2` and amenable.
