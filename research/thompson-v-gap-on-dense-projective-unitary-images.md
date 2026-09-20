---
rg: 2
id: thompson-v-gap-on-dense-projective-unitary-images
kind: claim
title: Homomorphisms of S4 *_Z2 S3 with dense image in PSU(k) = Inn(su(k)) have relator defect bounded below uniformly in k
distinct_from:
  thompson-v-gap-on-dense-orthogonal-adjoint-images: that is the same gap for the family Inn(so(k)); this is the family Inn(su(k)) = PSU(k), whose complexified adjoint representation is the traceless part of u tensor u-bar rather than Lambda^2.
  thompson-v-gap-on-dense-symplectic-adjoint-images: that is the same gap for the family Inn(sp(k)); this is the unitary family.
  thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups: that proves witnesses reduce to dense images in classical adjoint groups; this is one of the three resulting gap statements, left open.
  thompson-v-is-not-mf: that is the conjunction of this gap with the orthogonal and symplectic gaps; this is the SU third alone, which the target implies but does not reduce to.
---

**OPEN.**

Notation is as in `thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap(SU)`).** There is `eps > 0` with the following property. Let `k >= 2`, and fix an
`Inn(su(k))`-invariant inner product on `su(k)`. Let `tau : G0 -> Inn(su(k)) = PSU(k)` be a
homomorphism with dense image. Then

```text
max_(5 <= i <= 8) || tau(r_i) - 1 ||_op >= eps .
```

**Equivalent projective form.** It suffices to consider the adjoint action on `su(k)`. By the
eigenvalue remark in the parent claim, a small defect means the relator images are close to scalars.
So `Gap(SU)` says: there is no sequence of projective unitary representations `G0 -> PU(k_j)`, with
dense image, such that every lift of each `r_i` is within `o(1)` of a scalar.

**Status.**
- `thompson-v-is-not-mf` implies this, by item 5 of the parent claim.
- Together with the SO and Sp gaps, this implies `thompson-v-is-not-mf`.
- Fixed `k` is gapped. Apply item 1 of `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes` to the
  complexified adjoint representation, which is nontrivial of dimension `k^2 - 1`. So only uniformity
  in `k` is open.
