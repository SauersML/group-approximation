---
rg: 2
id: subshift-el-transvection-conjugacy-full-group-equivalence
kind: claim
title: In G_X = EL_3(LC(X,F_2)⋊Z), the transvections e_13(1_A) and e_13(1_B) are conjugate iff A and B are equivalent under the topological full group, iff [1_A] = [1_B] in K^0(X,T)
distinct_from:
  subshift-crossed-product-k0-is-coinvariant-group: that computes the abelian group K_0 of the crossed product ring; this computes conjugacy classes of root transvections in the elementary group, and its proof does not use K_0.
  subshift-elementary-group-word-problem-degree: that is about the word problem of G_X; this identifies a family of conjugacy classes of G_X with a dynamical invariant.
artifacts:
  - research/artifacts/sk-free-3-conjugacy-problem-2026-09-13-part1.md
  - research/artifacts/sk-verify-14-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal subshift with shift `T`, let `R = LC(X,F_2) ⋊_T Z`, and let `G_X = EL_3(R)`. For clopen `A, B ⊆ X` the following are equivalent:

1. `e_13(1_A)` and `e_13(1_B)` are conjugate in `G_X`;
2. `1_A − 1_B = g∘T − g` for some `g ∈ C(X,Z)`, i.e. `[1_A] = [1_B]` in `K^0(X,T) = C(X,Z)/(1−T_*)C(X,Z)`;
3. `γ(A) = B` for some `γ` in the topological full group `[[T]]`.

**Consequences.**
- For every `X`, the `[[T]]`-equivalence problem for clopen sets many-one reduces to the conjugacy problem of `G_X`.
- The conjugacy classes of the root transvections `e_13(1_A)` correspond bijectively to the classes `[1_A]` (`A` clopen) in `K^0(X,T)`, so the Giordano–Putnam–Skau dimension group is visible inside `G_X` by conjugation.

**Proof outline.** Details are in the `-proof` route and in part 1 of the artifact.
- **(3 ⇒ 1).** `w = Σ_k 1_{γU_k} u^k` is a unit with `w 1_A w^{−1} = 1_{γA}`. In characteristic 2, `diag(w, w^{−2}, w) = diag(w, w^{−1}, 1)·diag(1, w^{−1}, w)` lies in `G_X` by the Whitehead identity, and it conjugates `e_13(1_A)` to `e_13(1_B)`.
- **(2 ⇒ 3).** Kakutani–Rokhlin towers over a clopen set on which `g` is constant have equally many `A`-levels and `B`-levels.
- **(1 ⇒ 2).** Apply the note's periodic finite models to return loops `x[a,b)` of long words. Rank equality makes the loop sums of `1_A − 1_B` vanish, and a Livšic argument then gives the continuous transfer function `g`.
- **Cross-check.** `1 ⇒ 2` also follows from `1_A R ≅ 1_B R` and `subshift-crossed-product-k0-is-coinvariant-group`.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived: (3 ⇒ 1) through the permutation unit and the characteristic-2 Whitehead diagonal; (2 ⇒ 3) through Kakutani–Rokhlin level matching; (1 ⇒ 2) through periodic finite models and the Livšic loop argument; and Lemma U. Route 2 through `K_0` is a consistent cross-check but is not needed. Wording W1 applied to the consequence on conjugacy classes. See `research/artifacts/sk-verify-14-2026-09-13-part2.md` §2.
