---
rg: 2
id: steinberg-pushed-marginal-sums-have-no-new-closure
kind: claim
title: Unweighted sums of the pushed Steinberg marginals recover only the existing balance identities
artifacts:
  - research/steinberg-pushed-marginal-sum-proof.md
distinct_from:
  steinberg-fox-recurrence-forces-zero-marginals: this rules out only closure by unweighted fiber and Mobius-orbit summation; the full pointwise system may still force both marginals to vanish.
---

**ESTABLISHED.**  Sum the explicit point and plane equations of
`steinberg-fox-marginal-pushes-are-explicit` over an entire affine fiber or
an entire orbit of the displayed fractional-linear coordinate.  After the
telescoping differences cancel, the resulting scalar equations are exactly

```text
T=A(0)-A(-1/2)+C(0)-C(-1/2),                         (SMS1)
```

and the already available one-dimensional `A` and `C` balance identities.
No equation produced by these unweighted sums fixes an absolute value of
`P` or `H`.  Thus plain summation cannot close the marginal-vanishing node;
one needs pointwise propagation, a weighted transform, or another input.

DERIVATION
steinberg-pushed-marginal-sum-proof
