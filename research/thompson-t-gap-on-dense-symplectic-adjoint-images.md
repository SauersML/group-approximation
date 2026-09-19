---
rg: 2
id: thompson-t-gap-on-dense-symplectic-adjoint-images
kind: claim
title: Homomorphisms of Z/4 * Z/3 with dense image in Sp(k)/{+-1} have Lochak--Schneps relator defect bounded below uniformly in k
distinct_from:
  thompson-t-gap-on-dense-projective-unitary-images: that is the same level-T gap for PSU(k); this is the symplectic family, whose complexified adjoint representation is Sym^2 of the standard one.
  thompson-t-gap-on-dense-orthogonal-adjoint-images: that is the same level-T gap for Inn(so(k)); this is the symplectic family.
  thompson-t-triangle-gap-on-dense-symplectic-adjoint-images: that is the gap for honest Delta(4,3,5)-homomorphisms, which this one implies; this ranges over all Z/4 * Z/3 homomorphisms, pentagon defect included.
  thompson-v-gap-on-dense-symplectic-adjoint-images: that is the symplectic gap for V over S4 *_Z2 S3; this is the symplectic gap for T over Z/4 * Z/3.
  thompson-t-has-full-mf-radical: that is equivalent to the conjunction of the three level-T gaps; this is the Sp third alone.
---

**OPEN.**

Notation is as in `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap_T(Sp)`).** There is `eps > 0` with the following property. Let `k >= 1`, fix an
invariant inner product on `sp(k)`, and let `tau : Z/4 * Z/3 -> Sp(k)/{+-1}` be a homomorphism with
dense image. Then

```text
max( ||tau(r_1) - 1||, ||tau(r_2) - 1||, ||tau((ba)^5) - 1|| ) >= eps .
```

**Status.**
- `thompson-t-has-full-mf-radical` implies this, by item 1 of the parent claim.
- Together with the SU and SO gaps, this implies `thompson-t-has-full-mf-radical`.
- It implies `thompson-t-triangle-gap-on-dense-symplectic-adjoint-images`, by item 3 of the parent claim.
- Each fixed `k` is gapped, by `delta_(k(2k+1)) > 0` applied to the adjoint representation. So only
  uniformity in `k` is open.
- It fails exactly when there are dense homomorphisms into `Sp(k_j)/{+-1}` whose three relator images
  tend to `1`. Such a sequence would make `T` MF.
