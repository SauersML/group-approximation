---
rg: 2
id: lamplighter-cube-embeds-in-leavitt-units-proof
kind: route
title: A wandering cylinder for a Thompson F element and an involution inside it generate the lamplighter
target: lamplighter-cube-embeds-in-binary-leavitt-unit-group
requires: []
---

Write `[w]` for the cylinder of infinite binary words beginning with `w`.

1. **The shift.** Let `t` be the prefix replacement `0w ↦ 00w`, `10w ↦ 01w`, `11w ↦ 1w`. The
   images partition the Cantor set, so `t in F <= V`. Put `C = [10]`.
   - `t(C) = [01]` and `t([0^n 1]) = [0^(n+1) 1]`, so `t^n(C) = [0^n 1]` for `n >= 1`.
   - `t^(-1)` is `00w ↦ 0w`, `01w ↦ 10w`, `1w ↦ 11w`, so `t^(-n)(C) = [1^(n+1) 0]`.
   - All `t^n(C)`, `n in Z`, are pairwise disjoint, and `t` has infinite order.
2. **The lamps.** Let `a in V` swap `[100]` and `[101]` and fix everything else. Then
   `a_n = t^n a t^(-n)` is an involution supported in `t^n(C)`. Disjoint supports make the
   `a_n` commute and generate `⊕_(n in Z) Z/2`. A finite product of distinct `a_n` moves every
   cylinder it involves, so it is nontrivial.
3. **The semidirect product.** Conjugation by `t` shifts the `a_n`. The subgroup `⟨a_n⟩` is
   torsion, so it meets `⟨t⟩` trivially. Hence `⟨a, t⟩ ≅ Z/2 ≀ Z`.
4. **The cube.** Conjugating by the prefix maps `[w] -> [w_i w]`, `w_1 = 00`, `w_2 = 01`,
   `w_3 = 1`, gives three copies supported in the disjoint cylinders `[w_i]`. They commute, so
   they generate `(Z/2 ≀ Z)^3`.
5. **Into the units.** A bijection `u_i ↦ v_i` between complete prefix codes defines the unit
   `Σ_i s_(v_i) t_(u_i)` of `L_(F_2)(1,2)`, with inverse `Σ_i s_(u_i) t_(v_i)`. Composition in
   `V` matches the product, so `V <= L_(F_2)(1,2)^x`.
