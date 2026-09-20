---
rg: 2
id: thompson-t-gap-on-dense-orthogonal-adjoint-images
kind: claim
title: Homomorphisms of Z/4 * Z/3 with dense image in Inn(so(k)) have Lochak--Schneps relator defect bounded below uniformly in k
distinct_from:
  thompson-t-gap-on-dense-projective-unitary-images: that is the same level-T gap for PSU(k); this is the orthogonal family, whose complexified adjoint representation is Lambda^2 of the standard one.
  thompson-t-gap-on-dense-symplectic-adjoint-images: that is the same level-T gap for Inn(sp(k)); this is the orthogonal family.
  thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images: that is the gap for honest Delta(4,3,5)-homomorphisms, which this one implies; this ranges over all Z/4 * Z/3 homomorphisms, pentagon defect included.
  thompson-v-gap-on-dense-orthogonal-adjoint-images: that is the orthogonal gap for V over S4 *_Z2 S3; this is the orthogonal gap for T over Z/4 * Z/3.
  thompson-t-has-full-mf-radical: that is equivalent to the conjunction of the three level-T gaps; this is the SO third alone.
---

**OPEN.**

Notation is as in `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap_T(SO)`).** There is `eps > 0` with the following property. Let `k >= 3` with
`k != 4`, so that `so(k)` is simple, and fix an invariant inner product. Let
`tau : Z/4 * Z/3 -> Inn(so(k))` be a homomorphism with dense image. `Inn(so(k))` is `SO(k)` or
`SO(k)/{+-1}`. Then

```text
max( ||tau(r_1) - 1||, ||tau(r_2) - 1||, ||tau((ba)^5) - 1|| ) >= eps .
```

**Status.**
- `thompson-t-has-full-mf-radical` implies this, by item 1 of the parent claim.
- Together with the SU and Sp gaps, this implies `thompson-t-has-full-mf-radical`.
- It implies `thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images`, by item 3 of the parent claim.
- Each fixed `k` is gapped, by `delta_(k(k-1)/2) > 0` applied to the adjoint representation. So only
  uniformity in `k` is open.
- It fails exactly when there are dense homomorphisms into `Inn(so(k_j))` whose three relator images
  tend to `1`. Such a sequence would make `T` MF.
