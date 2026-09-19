---
rg: 2
id: exact-mf-radical-over-z-via-sofic-non-mf-titz-witzel-kernel
kind: route
title: Take the smallest Titz--Witzel kernel times Z once that same kernel is sofic and not MF
target: torsion-free-sofic-exact-mf-radical-over-z
requires:
  - titz-witzel-kernel-sofic
  - titz-witzel-smallest-kernel-not-mf
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
  - finite-outer-order-radical-witnesses-cross-alekseev-thom
  - mf-positive-controls
---

This corrects `torsion-free-sofic-exact-mf-radical-via-titz-witzel`. That route requires the
existential `titz-witzel-exact-kazhdan-mf-radical-over-z` (some residual is not MF) and the
soficity of the specific kernel `Gamma_1^2`. Both can hold for different residuals without
giving a witness; see `titz-witzel-smallest-kernel-not-mf`. Here both properties are asked of
the same kernel.

Put `K = Gamma_1^2`.

1. By `titz-witzel-simple-kazhdan-cat0-lattices-exist`, `K` is finitely presented, torsion-free,
   infinite (so nontrivial), simple and Kazhdan.
2. `K` is sofic by `titz-witzel-kernel-sofic`.
3. `Rad_MF(K) = K`. Let `f : K -> M` be a homomorphism to an MF group. Its image is a subgroup of
   `M`, so it is MF by `mf-positive-controls`. Its kernel is normal in the simple group `K`, so it
   is `1` or `K`. If it were `1`, then `K` would be isomorphic to its image and so MF, contradicting
   `titz-witzel-smallest-kernel-not-mf`. So `f` is trivial.
4. Now `K` is a nontrivial, finitely presented, torsion-free, sofic Kazhdan group with
   `Rad_MF(K) = K`. Part 2 of `finite-outer-order-radical-witnesses-cross-alekseev-thom` (the
   converse direction) shows that `(K x Z, K)` satisfies `(TFZ1)`.

It also satisfies the preferred strengthening: `K` is finitely presented, and it is normally
generated in `K x Z` by any nonidentity element of `K`, by simplicity. `∎`

By part 3 of the same theorem, completing this route also answers Alekseev--Thom Open Problem 6.1.
