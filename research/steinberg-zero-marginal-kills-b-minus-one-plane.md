---
rg: 2
id: steinberg-zero-marginal-kills-b-minus-one-plane
kind: claim
title: Every zero-marginal Steinberg Fox solution vanishes on the b=-1 plane
artifacts:
  - research/steinberg-b-minus-one-plane-proof.md
distinct_from:
  steinberg-three-zero-families-propagate-all-chords: this supplies a new full affine plane of zeros for every odd prime; it does not yet propagate that plane to every b-value.
---

**ESTABLISHED.**  Let `p` be odd and let `f:F_p^3 -> F_p` satisfy both
Steinberg chord Fox rows with `P=H=0`.  Then

```text
f(A,-1,C)=0                    for every A,C in F_p.   (SBP1)
```

The proof first pushes the `Y` row through the plane marginal.  For
`g=(1-q)f`, the generic branch of `(SMP5)` covers every
`(A,-1,C)` with `A!=-1/2` and `C!=0`.  The source identity fills
`A=-1/2`, and `P_g=0` fills `C=0`.  Thus `f` is independent of `A` on
that plane.  The projective `r` recurrence `(SYZ4)` moves every nonzero
`C` to `-1`, where `(SYZ1)` is zero, and the point marginal kills the
remaining `C=0` value.

As immediate further zero families,

```text
f(A,1/4,1)=0,                 f(a,2a-1,1)=0.          (SBP2)
```

The first follows by pushing `Y` through `P` on the exceptional point
fiber `b=1`; the second follows by evaluating `X` on the target line and
using `(SBP1)` for the `A(1-q)` summand.

DERIVATION
steinberg-b-minus-one-plane-proof
