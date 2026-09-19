---
rg: 2
id: titz-witzel-smallest-kernel-not-mf
kind: claim
title: The smallest Titz--Witzel simple Kazhdan kernel is not MF
distinct_from:
  titz-witzel-exact-kazhdan-mf-radical-over-z: that is existential over the five residuals, so it can be witnessed by a residual other than the one proved sofic; this fixes the same kernel Gamma_1^2 as titz-witzel-kernel-sofic, which is what the Titz--Witzel route to the goal actually needs.
  titz-witzel-residual-is-mf: that asserts the MF alternative for some residual; this asserts the non-MF alternative for the smallest residual, so the two are compatible unless the MF residual is Gamma_1^2.
artifacts:
  - research/titz-witzel-kernel-sofic.md
  - research/torsion-free-sofic-exact-mf-radical-via-titz-witzel.md
  - research/finite-outer-order-radical-witnesses-cross-alekseev-thom.md
---

**OPEN.** Let `K = Gamma_1^2` be the smallest Titz Mite--Witzel lattice, the kernel fixed in
`titz-witzel-kernel-sofic`. The claim is that `K` does not embed in the unitary group of any norm
corona `prod_n M_(k_n)(C) / directSum_n M_(k_n)(C)`.

**Why this node exists (route mis-specification).** The recorded Titz--Witzel route
`torsion-free-sofic-exact-mf-radical-via-titz-witzel` requires
- `titz-witzel-kernel-sofic`, which is about `Gamma_1^2`, and
- `titz-witzel-exact-kazhdan-mf-radical-over-z`, whose `(TWE1)` is existential: **some**
  residual `K'` has `Rad_MF(K' x Z) = K'`, which by its correction means that `K'` is not MF.

If `Gamma_1^2` is sofic and MF while a different residual `K'` is non-MF but not known to be
sofic, both prerequisites hold. Yet `Gamma_1^2 x Z` is then MF with `Rad_MF = 1`, and `K' x Z` is
not known to be sofic, so no witness results. The route therefore does not follow from its listed
requirements. The corrected route
`exact-mf-radical-over-z-via-sofic-non-mf-titz-witzel-kernel` pins both properties to the same
kernel through the present claim.

**Equivalent forms.**
- By simplicity, `K` is not MF exactly when `Rad_MF(K) = K`. A homomorphism `f : K -> M` into an MF
  group has image in an MF group, and the image is MF by `mf-positive-controls`. The kernel of `f`
  is normal in the simple group `K`. So either `f` is trivial or `f` is injective, and the second
  case makes `K` MF.
- By the correction in `titz-witzel-exact-kazhdan-mf-radical-over-z`, it is exactly the
  statement `Rad_MF(Gamma_1^2 x Z) = Gamma_1^2`.

**Calibration.** With `titz-witzel-kernel-sofic`, this claim gives a positive answer to
Alekseev--Thom 6.1 (`finite-outer-order-radical-witnesses-cross-alekseev-thom`, part 3). Alone,
it says that a finitely presented simple Kazhdan group is not MF. This is consistent with every
recorded obstruction:
- exact unitary models are trivial by Malcev (`titz-witzel-residual-is-mf`, Attempts);
- the Radu product-of-trees core is MF (`radu-bmw-lattice-is-mf`), so non-MF of `K` cannot be
  detected on that core.

## Attempts
