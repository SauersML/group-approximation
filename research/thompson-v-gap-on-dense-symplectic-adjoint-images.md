---
rg: 2
id: thompson-v-gap-on-dense-symplectic-adjoint-images
kind: claim
title: Homomorphisms of S4 *_Z2 S3 with dense image in Inn(sp(k)) = Sp(k)/{+-1} have relator defect bounded below uniformly in k
distinct_from:
  thompson-v-gap-on-dense-projective-unitary-images: that is the same gap for Inn(su(k)) = PSU(k); this is the compact symplectic family, acting on Sym^2 C^(2k).
  thompson-v-gap-on-dense-orthogonal-adjoint-images: that is the same gap for Inn(so(k)); this is the symplectic family.
  thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups: that proves witnesses reduce to dense images in classical adjoint groups; this is one of the three resulting gap statements, left open.
  thompson-v-is-not-mf: that is the conjunction of the three gaps; this is the Sp third alone.
---

**OPEN.**

Notation is as in `thompson-v-mf-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap(Sp)`).** There is `eps > 0` with the following property. Let `k >= 1`, and fix an
`Inn(sp(k))`-invariant inner product on `sp(k)`. Let `tau : G0 -> Inn(sp(k)) = Sp(k)/{+-1}` be a
homomorphism with dense image. Then

```text
max_(5 <= i <= 8) || tau(r_i) - 1 ||_op >= eps .
```

**Status.**
- `thompson-v-is-not-mf` implies this, by item 5 of the parent claim.
- Together with the SU and SO gaps, this implies `thompson-v-is-not-mf`.
- Only uniformity in `k` is open.
