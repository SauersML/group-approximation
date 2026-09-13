---
rg: 2
id: kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers-proof
kind: route
title: Split by whether the centralizing element has a power in the subgroup, using the dimension count or the translation character
target: kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers
requires: [vcd-two-groups-contain-no-kazhdan-commuting-pairs]
---

Let `c in C_K(Gamma)` with `c != 1`. Since `K` is torsion-free, `c` has infinite order.

**Case A: `<c> cap Gamma = 1`.** Then `<c>` and `Gamma` commute and meet trivially, and `Gamma` is
infinite and Kazhdan. (CD2) of `vcd-two-groups-contain-no-kazhdan-commuting-pairs` (with
`G_0 = K`) makes `<c>` finite. That is a contradiction.

**Case B: `c^m in Gamma` for some `m >= 1`.** Put `d = c^m`, a nontrivial element of the centre of
`Gamma`.

- *`d` is hyperbolic.* The action of `K` is proper and cocompact, so every element of `K` is
  semisimple (Bridson--Haefliger, *Metric spaces of non-positive curvature*, Part II, Chapter 6;
  exact item not re-read here).
  - An elliptic element fixes a point, so it lies in a finite stabilizer and has finite order.
  - `d != 1` and `K` is torsion-free, so `d` is hyperbolic, with translation length `|d| > 0`.
- *The translation character.* `Min(d)` is isometric to a product `Y x R`, on which `d` acts as
  `(y,t) |-> (y, t + |d|)`. Every isometry commuting with `d` preserves `Min(d)` and the product
  decomposition, and acts on the `R` factor by a translation (Bridson--Haefliger II.6.8, as
  recalled, not re-read). The translation parts compose additively. So
  `tau : C_K(d) -> R` is a homomorphism with `tau(d) = |d| != 0`.
- *Contradiction.* `Gamma <= C_K(d)`, because `d` is central in `Gamma`. So `tau` restricts to a
  homomorphism `Gamma -> R` that is nonzero on `d in Gamma`. A Kazhdan group has finite
  abelianization, so every homomorphism to `R` vanishes.

Both cases are impossible, so `C_K(Gamma) = 1`. `QED`

**Instances.** The Titz Mite--Witzel kernels act freely and cocompactly on their CAT(0) buildings
of dimension two, so `cd <= 2` (`vcd-two-groups-contain-no-kazhdan-commuting-pairs`, Instances).

**Model test.** In `F_2 x Z`, which is torsion-free, of dimension two and CAT(0), the centralizer
of the infinite subgroup `F_2 x 1` is `Z`. This is consistent: `F_2` is not Kazhdan, and the
theorem needs property (T) in both cases.
