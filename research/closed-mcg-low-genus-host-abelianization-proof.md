---
rg: 2
id: closed-mcg-low-genus-host-abelianization-proof
kind: route
title: Follow a subgroup down the forgetful tower to the first puncture where its image is nontrivial, where the image is a nontrivial free group
target: closed-mcg-low-genus-host-gives-infinite-abelianization
requires:
  - closed-mcg-punctured-host-forgetful-dichotomy
---

Notation is that of `closed-mcg-punctured-host-forgetful-dichotomy`. Write
`ρ′_i: L′ → PMod(S_(h,i))` for `ρ′` followed by forgetting all punctures but
the first `i`, so `ρ′_(i−1) = p_i ∘ ρ′_i`, where
`p_i: PMod(S_(h,i)) → PMod(S_(h,i−1))` forgets the `i`-th puncture.

**Standard inputs (not re-read for this route).**
- **(I1) Birman exact sequence** (Farb--Margalit, *Primer*, Thm 4.6): if
  `χ(S_(h,i−1)) < 0`, then `ker p_i = Push(π_1(S_(h,i−1))) ≅ π_1(S_(h,i−1))`.
- **(I2)** `PMod(S_(0,i))` is trivial for `i ≤ 3`, and
  `PMod(S_(1,1)) ≅ SL_2(Z)`.
- **(I3)** `SL_2(Z)` has a free subgroup of finite index.
- **(I4)** The fundamental group of a surface with at least one puncture is free.
  Subgroups of free groups are free (Nielsen--Schreier). A nontrivial free group
  surjects onto `Z`: send one basis element to `1` and the others to `0`.

**Lemma.** Let `h ≤ 1`, let `0 ≤ i_0 ≤ m` with `2 − 2h − i_0 < 0`, and let
`A ≤ L′` be nontrivial with `ρ′_(i_0)(A) = 1`. Then `A` surjects onto `Z`.

*Proof.*
1. `ρ′_m = ρ′` is injective and `A ≠ 1`, so `ρ′_m(A) ≠ 1`. Let `i` be the least
   index with `ρ′_i(A) ≠ 1`. Then `i_0 < i ≤ m`.
2. `ρ′_(i−1)(A) = 1`, so `ρ′_i(A) ≤ ker p_i`.
3. `i − 1 ≥ i_0`, so `χ(S_(h,i−1)) = 2 − 2h − (i − 1) ≤ 2 − 2h − i_0 < 0`. By
   (I1), `ker p_i ≅ π_1(S_(h,i−1))`.
4. Since `h ≤ 1`, the inequality `2 − 2h − i_0 < 0` forces `i_0 ≥ 1`. So
   `i − 1 ≥ 1`, the surface `S_(h,i−1)` is punctured, and `π_1(S_(h,i−1))` is
   free by (I4).
5. So `ρ′_i(A)` is a nontrivial free group, and `A ↠ ρ′_i(A) ↠ Z` by (I4). ∎

**Proof of (a).** Let `h = 0` and `A ≤ L′` be nontrivial.
1. `m ≥ 4`. Otherwise `ρ′` lands in `PMod(S_(0,m))`, which is trivial by (I2).
   But `ρ′` is injective on the infinite group `L′`.
2. `ρ′_3(A) ≤ PMod(S_(0,3)) = 1` by (I2). The index `i_0 = 3 ≤ m` has
   `2 − 0 − 3 < 0`.
3. By the Lemma, `A` surjects onto `Z`.
4. Taking `A = L′`, which is nontrivial since it has finite index in the infinite
   group `Mod(S_g)`, gives `L′ ↠ Z`.
5. A nontrivial finite cyclic subgroup cannot surject onto `Z`. So `L′` is
   torsion-free.

**Proof of (b).** Let `h = 1` and `A ≤ L′` be infinite. Note `ρ′_1(A) ≤
PMod(S_(1,1)) ≅ SL_2(Z)` by (I2).
- **Case 1: `ρ′_1(A)` is infinite.**
  1. Let `F ≤ SL_2(Z)` be free of finite index (I3), transported to
     `PMod(S_(1,1))`.
  2. Put `A_0 := A ∩ ρ′_1^-1(F)`. It has finite index in `A`, and
     `ρ′_1(A_0) = ρ′_1(A) ∩ F`.
  3. `ρ′_1(A) ∩ F` has finite index in the infinite group `ρ′_1(A)`, so it is
     infinite. It is a subgroup of the free group `F`, hence a nontrivial free
     group by (I4).
  4. So `A_0 ↠ ρ′_1(A_0) ↠ Z`.
- **Case 2: `ρ′_1(A)` is finite.**
  1. Put `A_0 := A ∩ ker ρ′_1`. Its index in `A` is `|ρ′_1(A)|`, which is finite.
  2. `A` is infinite, so `A_0` is nontrivial.
  3. `ρ′_1(A_0) = 1` and `i_0 = 1` has `2 − 2 − 1 < 0`. By the Lemma, `A_0`
     surjects onto `Z`.
- **The group `L″`.** `L′` is infinite, since it has finite index in
  `Mod(S_g)`. Applying the above to `A = L′` gives a finite-index `L″ ≤ L′`
  with `L″ ↠ Z`. `L″` has finite index in `Mod(S_g)`.

**Consequence.** In either genus some finite-index subgroup of `Mod(S_g)`
surjects onto `Z`, so its abelianization is infinite. The equivalent
formulation in the target is the contrapositive, combined with the dichotomy's
statement that shape A needs `h ≥ g`. `∎`
