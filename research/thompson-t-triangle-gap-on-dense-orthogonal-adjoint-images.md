---
rg: 2
id: thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images
kind: claim
title: Homomorphisms of the triangle group Delta(4,3,5) with dense image in Inn(so(k)) keep the Lochak--Schneps words r_1, r_2 a uniform distance from 1
distinct_from:
  thompson-t-gap-on-dense-orthogonal-adjoint-images: that is the level-T gap over Z/4 * Z/3, which implies this one; this ranges only over honest Delta-homomorphisms.
  thompson-t-triangle-gap-on-dense-projective-unitary-images: that is the same Delta-level gap for PSU(k); this is the orthogonal family.
  thompson-t-triangle-gap-on-dense-symplectic-adjoint-images: that is the same Delta-level gap for Inn(sp(k)); this is the orthogonal family.
  thompson-t-triangle-genuine-rep-relator-gap: that is (R_Delta), which is equivalent to the conjunction of the three Delta-level gaps; this is the SO third alone.
---

**OPEN.**

Notation is as in `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap_Delta(SO)`).** There is `eps > 0` with the following property. Let `k >= 3` with
`k != 4`, and let `tau : Delta(4,3,5) -> Inn(so(k))` be a homomorphism with dense image. Then

```text
max( ||tau(r_1) - 1||, ||tau(r_2) - 1|| ) >= eps
```

in any invariant inner product.

**Status.**
- (R_Delta) implies this, and together with the SU and Sp gaps it implies (R_Delta). Both directions
  are item 2 of the parent claim.
- It follows from `thompson-t-gap-on-dense-orthogonal-adjoint-images`.
- Each fixed `k` is gapped, by `gamma_(k(k-1)/2) > 0`. So only uniformity in `k` is open.
- **Where `k = 3` sits.** Dense homomorphisms `Delta -> SO(3)` exist.
  - *Example.* Take a spherical triangle with angles `3 pi/4`, `pi/3` and `3 pi/5`. The angle sum
    exceeds `pi`, so the triangle exists. Rotations by twice these angles about its vertices have
    orders 4, 3 and 5, and their product is the identity. This gives `phi : Delta -> SO(3)`.
  - *Its image is infinite.* A finite subgroup of `SO(3)` containing elements of orders 4 and 5 is cyclic
    or dihedral. In either case the images of `a` and `b` lie in the cyclic rotation part, so the image
    is abelian, hence trivial because `Delta` is perfect.
  - *Its image is dense.* The closed infinite subgroups of `SO(3)` are `SO(2)`, `O(2)` and `SO(3)`. The
    first two are solvable, which again forces the image to be trivial.

  Every such
  homomorphism, and every representation of `SO(3)` pulled back along it, has defect at least
  `min(1/2, gamma_3/2)` (item 5 of the parent claim). So the whole `SO(3)` layer is gapped at once, and
  a counterexample needs `k_j -> infinity`.
