---
rg: 2
id: thompson-t-gap-on-dense-projective-unitary-images
kind: claim
title: Homomorphisms of Z/4 * Z/3 with dense image in PSU(k) have Lochak--Schneps relator defect bounded below uniformly in k
distinct_from:
  thompson-t-gap-on-dense-orthogonal-adjoint-images: that is the same level-T gap for the family Inn(so(k)); this is the family PSU(k) = Inn(su(k)).
  thompson-t-gap-on-dense-symplectic-adjoint-images: that is the same level-T gap for the family Inn(sp(k)); this is the unitary family.
  thompson-t-triangle-gap-on-dense-projective-unitary-images: that is the gap for honest Delta(4,3,5)-homomorphisms, where (ba)^5 = 1 exactly, and this one implies it; this ranges over all Z/4 * Z/3 homomorphisms and includes the pentagon defect.
  thompson-v-gap-on-dense-projective-unitary-images: that is the PSU gap for V over S4 *_Z2 S3; this is the PSU gap for T over Z/4 * Z/3, and no known map gives an implication either way.
  thompson-t-has-full-mf-radical: that is equivalent to the conjunction of this gap with the SO and Sp gaps; this is the SU third alone, which the target implies but does not reduce to.
---

**OPEN.**

Notation is as in `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`.

**Statement (`Gap_T(SU)`).** There is `eps > 0` with the following property. Let `k >= 2`, fix an
`Inn(su(k))`-invariant inner product on `su(k)`, and let `tau : Z/4 * Z/3 -> PSU(k)` be a homomorphism
with dense image. Then

```text
max( ||tau(r_1) - 1||, ||tau(r_2) - 1||, ||tau((ba)^5) - 1|| ) >= eps .
```

**Projective form.** Equivalently, there is no sequence of pairs `(A_j, B_j)` in `U(k_j)` with the
following three properties:
- `A_j^4` and `B_j^3` are scalars;
- the pair generates a subgroup that is dense modulo scalars;
- every lift of `r_1`, `r_2` and `(ba)^5` is within `o(1)` of a scalar.

**Status.**
- `thompson-t-has-full-mf-radical` implies this, by item 1 of the parent claim.
- Together with the SO and Sp gaps, this implies `thompson-t-has-full-mf-radical`.
- It implies `thompson-t-triangle-gap-on-dense-projective-unitary-images`, by item 3 of the parent claim.
- Each fixed `k` is gapped. Apply `delta_(k^2 - 1) > 0` to the complexified adjoint representation. So
  only uniformity in `k` is open.
- It fails exactly when there are dense homomorphisms `tau_j : Z/4 * Z/3 -> PSU(k_j)` whose three
  relator images tend to `1`. Such a sequence would make `T` MF, by item 6 of
  `lie-closure-trichotomy-without-finite-quotients`.
