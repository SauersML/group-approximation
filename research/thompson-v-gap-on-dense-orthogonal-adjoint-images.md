---
rg: 2
id: thompson-v-gap-on-dense-orthogonal-adjoint-images
kind: claim
title: Homomorphisms of S4 *_Z2 S3 with dense image in Inn(so(k)) have relator defect bounded below uniformly in k
distinct_from:
  thompson-v-gap-on-dense-projective-unitary-images: that is the same gap for Inn(su(k)) = PSU(k); this is the orthogonal family, acting on Lambda^2 R^k.
  thompson-v-gap-on-dense-symplectic-adjoint-images: that is the same gap for Inn(sp(k)); this is the orthogonal family.
  thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups: that proves witnesses reduce to dense images in classical adjoint groups; this is one of the three resulting gap statements, left open.
  thompson-v-is-not-mf: that is the conjunction of the three gaps; this is the SO third alone.
---

**OPEN.**

Notation is as in `thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap(SO)`).** There is `eps > 0` with the following property. Let `k >= 3` with
`k != 4`, and fix an `Inn(so(k))`-invariant inner product on `so(k)`. Let
`tau : G0 -> Inn(so(k))` be a homomorphism with dense image. Then

```text
max_(5 <= i <= 8) || tau(r_i) - 1 ||_op >= eps .
```

`Inn(so(k))` is `SO(k)/{+-1}`: for odd `k` the centre is trivial, and for even `k` it is `{+-1}`.

**Status.**
- `thompson-v-is-not-mf` implies this, by item 5 of the parent claim.
- Together with the SU and Sp gaps, this implies `thompson-v-is-not-mf`.
- Only uniformity in `k` is open.
