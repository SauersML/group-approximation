---
rg: 2
id: free-minimal-subshift-elementary-groups-are-simple-kazhdan-proof
kind: route
title: Box-tower root detection plus Følner rank models
target: free-minimal-subshift-elementary-groups-are-simple-kazhdan
requires: [free-minimal-crossed-products-are-simple-with-rank-models, rank-modelled-simple-rings-give-linear-sofic-projective-el, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/free-minimal-subshift-elementary-groups-2026-09-13.md
---

The artifact, Sections 1 and 2, gives the proof.

1. **Kazhdan.** `R` is generated as a ring by `u_i^(±1)`, the letter cylinders and a primitive
   element of `F_q`. Ershov--Jaikin-Zapirain applies.
2. **Infinite.** `e_12(LC(X, F_q)) <= G`.
3. **Centre and linear soficity.** The first and second required claims give `Z(R) = F_q`, the
   centre of `G`, and an embedding of `S` in a rank ultraproduct.
4. **Long return times.** Freeness and compactness: a cylinder of large radius meeting a translate
   by `g` would force `g`-periodic limit points.
5. **Box towers.** Put `E_ab(W) = chi_(τ^a W) u^(a-b)` for `a, b ∈ B_m`. These are matrix units
   over `LC(U, F_q)` once `U` has return times `> 2m`.
   - Absorption: propagation `w` moves `B_m(U)` into `B_(m+w)(U)`.
6. **A localized commutator.** Some root `e_ij(s)` fails to commute with a noncentral `g ∈ N`,
   where `s` is a cylinder indicator times `u^(0 or ±e_i)`. Such `s` lie in `B_1(U)` for towers with
   long return times. The commutator `k = [g, e_ij(s)] ∈ N` lives in
   `M_3(B_(1+w)(U)) ≅ LC(U, M_D(F_q))`.
7. **Case 1.** A non-scalar local value of `k` generates `SL_D(F_q)` inside `N`, since `D >= 27` and
   `PSL_D` is simple. So `e_12(chi_W) ∈ N`.
8. **Case 2.** If all local values are scalar, `k = c 1_3` with `c` a unit of `LC(X)`. Then
   `r = chi_Y u^(e_1)`, with `Y` just outside the tower, satisfies `c r c^(-1) = λ_0^(-1) r`, and
   `[k, e_12(r)]` is a nonzero root in `N`.
9. **Conclusion.** Level ideals and simplicity of `R` give `N = G`.
