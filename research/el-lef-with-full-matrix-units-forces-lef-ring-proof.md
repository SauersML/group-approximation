---
rg: 2
id: el-lef-with-full-matrix-units-forces-lef-ring-proof
kind: route
title: Reach rank 2N inside EL_N through a matrix-unit corner, apply the rank-four theorem to the corner ring, and transfer LEF back through fullness
target: el-lef-with-full-matrix-units-forces-lef-ring
requires:
  - lef-elementary-groups-force-lef-rings
  - tower-subshift-elementary-group-is-el-3k-of-base
---

Let `ε_ij ∈ R`, `i, j ∈ {1,2}`, satisfy `ε_ij ε_kl = δ_jk ε_il`, `ε_11 != 0` and `R ε_11 R = R`, and suppose
`EL_N(R)` is LEF for some `N >= 2`.

1. **Corner.** Let `e = ε_11 + ε_22`, an idempotent, and `S = ε_11 R ε_11`, a unital ring with unit `ε_11`.
   `Φ(z) = (ε_1i z ε_j1)_(i,j)` maps `eRe` to `M_2(S)`, and `Ψ((s_ij)) = sum_(i,j) ε_i1 s_ij ε_1j` maps back.
   - `Φ(z)Φ(z')` has `(i,j)` entry `sum_k ε_1i z ε_k1 ε_1k z' ε_j1 = ε_1i z e z' ε_j1 = ε_1i z z' ε_j1`, so `Φ`
     is multiplicative. It is additive, and `Φ(e) = (δ_ij ε_11)`.
   - `ΦΨ = id`, because `ε_1i ε_k1 = δ_ik ε_11`. `ΨΦ(z) = e z e = z`.
   So `eRe ≅ M_2(S)` as unital rings.
2. **Rank 2N inside rank N.** `g |-> (1-e)I_N + g` is an injective homomorphism `GL_N(eRe) -> GL_N(R)`,
   because `(1-e)r = r(1-e) = 0` for `r ∈ eRe`. It sends the elementary matrix `eI_N + rE_ij` of `GL_N(eRe)` to
   `I_N + rE_ij`, so it maps `EL_N(eRe)` into `EL_N(R)`. Through `Φ`, `EL_N(eRe) ≅ EL_N(M_2(S))`, and
   `EL_N(M_2(S)) = EL_(2N)(S)` by item 3 of `tower-subshift-elementary-group-is-el-3k-of-base` (every unital
   ring, `n = N >= 2`, `k = 2`). So `EL_(2N)(S)` is a subgroup of `EL_N(R)`, hence LEF.
3. **The corner ring is LEF.** Since `2N >= 4`, `lef-elementary-groups-force-lef-rings` applies to `S`.
4. **Matrices over S.** Let `F ⊆ M_m(S)` be finite. Let `E ⊆ S` consist of `0`, `1`, the entries of `F`, their
   negatives, all entrywise sums `A_ij + B_ij`, the products `A_ik B_kj` and all partial sums
   `sum_(k<=t) A_ik B_kj`, for `A, B ∈ F`. A LEF map `φ : E -> Q` into a finite unital ring, applied entrywise,
   is injective on `F`. By induction along the partial sums it preserves `0`, `1`, negatives, and the sums and
   products that stay in `F`. So `M_m(S)` is a LEF ring.
5. **Fullness.** Write `1 = sum_(i=1)^m x_i ε_11 y_i`. Put the column `u = (ε_11 y_1, …, ε_11 y_m)^T` and the
   row `v = (x_1 ε_11, …, x_m ε_11)`, so `vu = 1`. Then `f = uv ∈ M_m(S)` is idempotent, and
   `ψ(r) = u r v`, with entries `ε_11 y_i r x_j ε_11 ∈ S`, is a unital ring isomorphism `R -> f M_m(S) f`, with
   inverse `z |-> v z u`.
6. **Corners.** Given a finite `F ⊆ R`, apply step 4 to the finite set of `f`, the `ψ(r)` for `r ∈ F`, and their
   sums, products and the products with `f`. This gives a LEF map `Φ'` into a finite unital ring `Q'`.
   - `Φ'(f)` is idempotent.
   - `f ψ(r) = ψ(r) = ψ(r) f` gives `Φ'(ψ(r)) ∈ Φ'(f) Q' Φ'(f)`, a finite unital ring with unit
     `Φ'(f) = Φ'(ψ(1))`.
   So `r |-> Φ'(ψ(r))` is an injective LEF map for `F`, and `R` is a LEF ring. ∎
