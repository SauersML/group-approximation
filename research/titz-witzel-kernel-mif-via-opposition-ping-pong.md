---
rg: 2
id: titz-witzel-kernel-mif-via-opposition-ping-pong
kind: route
title: Ping-pong with strongly regular elements on the chambers at infinity makes the Titz Mite--Witzel kernels MIF, given three building premises
target: titz-witzel-kernels-are-mif
requires: [opposition-ping-pong-criterion-gives-mixed-identity-freeness, opposition-general-position-from-nowhere-domestic-dense-poles, strongly-regular-building-elements-are-opposition-proximal, cocompact-building-lattices-have-dense-strongly-regular-poles, titz-witzel-kernel-elements-are-nowhere-domestic-at-infinity, titz-witzel-simple-kazhdan-cat0-lattices-exist]
---

Fix `i, q`. Write `Γ̌ = Γ̌_i^q` and `X = X_i^q`.

1. **The action.** By `titz-witzel-simple-kazhdan-cat0-lattices-exist`,
   `Γ̌` acts freely and cocompactly on `X`. `X` is a locally finite exotic
   building of type `C̃₂` with thickness `q + 1 ≥ 3`, so it is thick. The action
   is proper, since it is free on a locally finite complex. `Γ̌` is infinite and
   simple.
2. **Type-preserving.** The type-preserving automorphisms form a normal
   subgroup of finite index in `Aut(X)` (Abramenko--Brown Prop. A.14, as cited
   in Caprace--Ciobotaru's proof of their Theorem 1.2; not re-read). Its
   intersection with `Γ̌` is normal of finite index in `Γ̌`. It is nontrivial,
   since `Γ̌` is infinite, so simplicity makes it all of `Γ̌`. So `Γ̌` acts by
   type-preserving automorphisms.
3. **The space.** Put `Z = Ch(∂X)` and `O` = opposition. By part (a) of
   `strongly-regular-building-elements-are-opposition-proximal`, `Z` is compact
   Hausdorff, `O` is open and every `O(c)` is dense.
4. **(D2).** By part (b) of the same claim, each strongly regular hyperbolic
   `a ∈ Γ̌` is proximal with poles `(c₊(a), c₋(a))`. By
   `cocompact-building-lattices-have-dense-strongly-regular-poles`, applied with
   `Γ = Γ̌` (steps 1 and 2 give its hypotheses), these pole pairs are dense in
   `O`.
5. **(D1).** This is `titz-witzel-kernel-elements-are-nowhere-domestic-at-infinity`.
6. **Conclusion.** By
   `opposition-general-position-from-nowhere-domestic-dense-poles`, (GP)
   holds for `Γ̌` on `Z`. By
   `opposition-ping-pong-criterion-gives-mixed-identity-freeness`, `Γ̌` is MIF.
   `∎`

**Why not Rybak's method.**
- **What it needs.** Rybak feeds rank-one elements (Caprace--Fujiwara
  Proposition 5.3) into the Petyt--Spriano--Zalloum curtain model; see
  `fp-simple-kac-moody-lattices-are-mif`.
- **Why `X` has none.** In a Euclidean building every geodesic line lies in an
  apartment (standard; not re-read). So every axis bounds a flat half-plane,
  and no isometry of `X` is rank one.
