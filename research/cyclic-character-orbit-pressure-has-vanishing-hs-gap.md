---
rg: 2
id: cyclic-character-orbit-pressure-has-vanishing-hs-gap
kind: claim
title: Cyclic character-orbit overflow has vanishing normalized-HS soundness
artifacts:
  - research/artifacts/adversarial-dimension-matched-hs-pcp-synthesis-2026-08-20.md
distinct_from:
  dimension-kleene-threshold-needs-amplification-envelope: that proves abstractly why an arbitrary positive post-halting threshold is insufficient; this gives an explicit scalar near-model whose threshold decays along the most natural cyclic character-orbit detector.
  lamp-character-orbit-separation: that uses exact character orbits to separate two lamp sites inside an already supplied approximation; this shows that a large exact character orbit does not by itself give a constant relation gap.
  same-model-supercritical-clifford-trigger: that seeks dimension pressure with pinned discrete Pauli spectra; this explains why a continuously movable cyclic phase is not an adequate replacement.
---

For every odd integer `p>=3`, consider the marked presentation fragment

```text
a^p=1,                    t a t^(-1)=a^3,                (CCO1)
```

with marked word `a`.  Exact character-orbit reasoning may force a large
orbit under multiplication by `3` modulo `p`, but `(CCO1)` has a
one-dimensional unitary assignment with the order relation exact, marked
distance tending to the maximum `2`, and conjugacy-relation defect tending to
zero.

Explicitly, take

```text
lambda_p=exp(2 pi i (p+1)/(2p)),       a=lambda_p, t=1.   (CCO2)
```

Then

```text
lambda_p^p=1,
|lambda_p-1| -> 2,
|t a t^(-1)a^(-3)-1|=|1-lambda_p^(-2)|
                    =2 sin(pi/p)=O(1/p).                 (CCO3)
```

Thus no dimension-independent normalized-Hilbert--Schmidt collapse of the
mark follows from these orbit relations.  Increasing the exact orbit size
also shrinks the available gap.  A dimension-reported Kleene compiler using
this cell would therefore fall into the post-halting threshold obstruction
unless some additional fixed-gap spectral pinning is supplied.

The fence is mechanism-specific: it does not rule out every finite abelian
register.  It rules out treating exact character-orbit cardinality as if it
were already a robust capacity test.  Exponent-two Pauli/Clifford packets
avoid this particular scalar path because their relevant spectra are pinned
at `+1` and `-1`.
