---
rg: 2
id: tate-diagonal-cone-is-weakly-contractible-wreath-object-proof
kind: route
title: Fixed cosets of the centralizer of σ plus Green imprimitivity and the Meyer–Nest obstruction functor
target: tate-diagonal-cone-is-weakly-contractible-wreath-object
requires: []
artifacts: [research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part1.md]
---

The full derivation is in `research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part1.md`, §2–3.

- **Group theory (Lemma 1).**
  - An order-`p` element `cσ` is conjugate to `σ` by `b` with `b_1 = 1` and `b_i = c_i b_(i−1)`.
    The relation `c_1 c_p ⋯ c_2 = 1` is exactly `(cσ)^p = 1`.
  - Centralizers are computed coordinatewise.
  - Fixed cosets are part 3, Lemma 4, conjugated.
- **Item 1.**
  - Over a finite `F` conjugate to `<σ>`, `C_0(W/H)` is a `c_0`-sum over orbits.
  - The fixed orbit contributes `id_C`.
  - Free orbits contribute objects `Ind_1^F Res 1_T ≃ 0`.
  - Over `F = 1` and over `Γ^p`, `q^*1_T` restricts to an inflation of `Res^G_1 1_T ≃ 0`.
- **Item 2.**
  - The projection `δ_H` is full, with corner `H ⋉_r Res A`.
  - Cut down to that corner, `j_r^W(ε ⊗ 1_A)` is the class of the inclusion
    `H ⋉_r A → W ⋉_r A`.
  - For `A = q^*1_T` this inclusion is `T(Δ) ⋊ G`.
- **Item 3.** Descent is triangulated, plus Baaj–Skandalis duality for finite abelian `G`
  (standard, not re-read).
- **Items 4 and 5.** These are read from Meyer–Nest, arXiv:math/0312292v3:
  - Thm. 4.7: `A ∈ CC` implies `N ⊗ A ≅ A`;
  - the obstruction functor on p. 24;
  - Thm. 5.2: Baum–Connes with coefficients iff the obstruction groups vanish;
  - Lemma 4.2: `CC` is a tensor ideal;
  - Thm. 8.5: weakly contractible objects vanish for a-T-menable groupoids. `W` is a finite extension
    of the a-T-menable `Γ^p`.
