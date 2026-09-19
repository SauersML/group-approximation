---
rg: 2
id: steinberg-coupled-plane-transfer-has-marginal-absorber
kind: claim
title: The first coupled projective plane transfer admits a nonzero zero-marginal absorber
artifacts:
  - research/steinberg-first-coupled-plane-transfer-absorber-proof.md
invalidates:
  - steinberg-first-coupled-plane-transfer-kills-two-planes
distinct_from:
  steinberg-plane-transfer-stalls-at-large-primes: that shows the logical transfer rule has no known endpoint from the first seed; this constructs a nonzero absorber even after both transferred planes are coupled and all intrinsic marginals are imposed.
  steinberg-zero-marginal-kills-b-minus-one-plane: that supplies the seed plane b=-1; this proves that one application of Y from that seed does not supply a second zero plane.
---

**ESTABLISHED FIREWALL.**  For every prime `p>=7` there is a zero-marginal
chord function `f:F_p^3 -> F_p` with `P_f=H_f=0` and `f|_(b=-1)=0` such
that the nonzero difference `g=(1-q)f` is supported on the three planes

```text
b in {-4,-4/5,0},
```

and satisfies the entire pointwise `Y` row on `b=-4`, including its
exceptional denominator.  Therefore `P_f=H_f=0`, the known plane `Z(-1)`,
and every `Y` equation on the first new plane do not force either transferred
plane to vanish.  Any second-plane proof must use pointwise `X` information
or `Y` on additional `b`-planes.

DERIVATION
steinberg-first-coupled-plane-transfer-absorber-proof
