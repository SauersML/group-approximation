---
rg: 2
id: thompson-t-triangle-gap-on-dense-projective-unitary-images
kind: claim
title: Homomorphisms of the triangle group Delta(4,3,5) with dense image in PSU(k) keep the Lochak--Schneps words r_1, r_2 a uniform distance from 1
distinct_from:
  thompson-t-gap-on-dense-projective-unitary-images: that is the level-T gap over Z/4 * Z/3, which implies this one; this ranges only over honest Delta-homomorphisms, where (ba)^5 = 1 exactly.
  thompson-t-triangle-gap-on-dense-orthogonal-adjoint-images: that is the same Delta-level gap for Inn(so(k)); this is PSU(k).
  thompson-t-triangle-gap-on-dense-symplectic-adjoint-images: that is the same Delta-level gap for Inn(sp(k)); this is PSU(k).
  thompson-t-triangle-genuine-rep-relator-gap: that is (R_Delta), which is equivalent to the conjunction of the three Delta-level gaps; this is the SU third alone.
---

**OPEN.**

Notation is as in `thompson-t-witnesses-are-dense-in-simple-adjoint-groups`, with
`Delta = <a, b | a^4, b^3, (ba)^5>`.

**Statement (`Gap_Delta(SU)`).** There is `eps > 0` with the following property. Let `k >= 2` and let
`tau : Delta -> PSU(k)` be a homomorphism with dense image. Then

```text
max( ||tau(r_1) - 1||, ||tau(r_2) - 1|| ) >= eps
```

in any `PSU(k)`-invariant inner product on `su(k)`.

**Projective form.** Equivalently, there is no sequence of projective unitary representations of
`Delta` in `PU(k_j)`, with dense image, such that every lift of `r_1` and `r_2` is within `o(1)` of a
scalar.

**Status.**
- (R_Delta) implies this, and together with the SO and Sp gaps it implies (R_Delta). Both directions
  are item 2 of the parent claim.
- It follows from `thompson-t-gap-on-dense-projective-unitary-images`.
- Each fixed `k` is gapped, by `gamma_(k^2 - 1) > 0`. So only uniformity in `k` is open.
- By item 5 of the parent claim, the images in a counterexample cannot be finite or virtually abelian,
  and they cannot come from one fixed compact group. A counterexample must be a sequence of Zariski-dense,
  infinite-image points of the `PU(k_j)` character varieties of `Delta`, with `k_j -> infinity`, on
  which `r_1` and `r_2` tend to scalars.
