---
rg: 2
id: thompson-t-triangle-gap-on-dense-symplectic-adjoint-images
kind: claim
title: Homomorphisms of the triangle group Delta(4,3,5) with dense image in Sp(k)/{+-1} keep the Lochak--Schneps words r_1, r_2 a uniform distance from 1
distinct_from:
  thompson-t-gap-on-dense-symplectic-adjoint-images: that is the level-T gap over Z/4 * Z/3, which implies this one; this ranges only over honest Delta-homomorphisms.
  thompson-t-triangle-gap-on-dense-projective-unitary-images: that is the same Delta-level gap for PSU(k); this is the symplectic family.
  thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images: that is the same Delta-level gap for Inn(so(k)); this is the symplectic family.
  thompson-t-triangle-genuine-rep-relator-gap: that is (R_Delta), which is equivalent to the conjunction of the three Delta-level gaps; this is the Sp third alone.
---

**OPEN.**

Notation is as in `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap_Delta(Sp)`).** There is `eps > 0` with the following property. Let `k >= 1` and let
`tau : Delta(4,3,5) -> Sp(k)/{+-1}` be a homomorphism with dense image. Then

```text
max( ||tau(r_1) - 1||, ||tau(r_2) - 1|| ) >= eps
```

in any invariant inner product.

**Status.**
- (R_Delta) implies this, and together with the SU and SO gaps it implies (R_Delta). Both directions
  are item 2 of the parent claim.
- It follows from `thompson-t-gap-on-dense-symplectic-adjoint-images`.
- Each fixed `k` is gapped, by `gamma_(k(2k+1)) > 0`. So only uniformity in `k` is open.
- **The case `k = 1`.** Here `Sp(1)/{+-1} = SO(3)`. The two-dimensional representations of `Delta`
  factor through the binary icosahedral group, so they have finite image and are not dense. Dense
  homomorphisms into `SO(3)` do exist, and they are gapped by `min(1/2, gamma_3/2)`, by item 5 of the
  parent claim.
