---
rg: 2
id: whole-face-sign-rounding-does-not-inherit-gap-contraction
kind: claim
title: Whole-face sign rounding has charged equality damage but does not inherit the Hamiltonian contraction
distinct_from:
  random-whole-face-pinchings-contract-transverse-l2: that proves strict contraction for the linear conditional expectations; this shows the nonlinear reflection projection can erase that gain.
  sequential-pinchings-have-sharp-linear-disturbance-loss: that accumulates coordinate pinching disturbance on a sparse Clifford cycle; this is a two-face uniform-gap obstruction to contraction after every spectral-sign step.
  random-anchor-contraction-does-not-yet-enter-the-diffuse-basin: that audits coordinate anchors and missing exact code blocks; this isolates the additional whole-face nonconvexity even after exact faces exist.
---

For a face expectation `Phi` and a reflection `B`, put

```text
X=Phi(B),       B'=sgn(X).
```

Then `B'` is a reflection commuting with the whole face and

```text
||B-B'||_2^2 <= 2||B-Phi(B)||_2^2.                       (WFS1)
```

Consequently, if two shared occurrences `B_1,B_2` are updated, possibly by
different whole faces, then

```text
||B_1'-B_2'||_2^2
 <= 3||B_1-B_2||_2^2
    +6||B_1-Phi_1(B_1)||_2^2
    +6||B_2-Phi_2(B_2)||_2^2.                            (WFS2)
```

Thus equality damage is quadratic in the equality and face-odd amplitudes,
exactly as suggested by the multi-PVM grading.  There is nevertheless no
strict transverse-energy contraction for the sign-rounded iteration from
the face-Hamiltonian gap alone.

Indeed, in `M_2` let `A` and `C` be traceless reflections whose Bloch axes
meet at an angle `phi in (0,pi/2)`, and let `Phi_A,Phi_C` be their commutant
pinchings.  Their common fixed space is the scalars.  On the traceless
subspace the average Hamiltonian has gap

```text
gamma=(1-cos(phi))/2>0.                                  (WFS3)
```

But

```text
sgn(Phi_A(C))=A,       sgn(Phi_C(A))=C.                  (WFS4)
```

Every random sign-rounded update therefore leaves the current reflection
equal to `A` or `C`; its squared distance from the common fixed space remains
exactly one.  The linear iteration contracts by `(RWF2)`, while the nonlinear
reflection iteration does not contract at all.

This example has order-one pair commutator energy.  It does not refute a
small-balanced-energy basin theorem; it proves that such a theorem must use
that smallness (or an operator tube/transversality estimate) in addition to
the exact face gap.  Moreover, changing a coordinate to commute with one
face generally breaks its own overlapping face PVM, so local
re-exactification still reopens shared-occurrence synchronization.
