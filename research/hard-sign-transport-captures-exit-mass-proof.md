---
rg: 2
id: hard-sign-transport-captures-exit-mass-proof
kind: route
title: Project the intertwining defect onto the positive target sign
target: hard-sign-transport-captures-exit-mass
requires:
  - fanizza-bad-atoms-have-symmetric-frames
  - fanizza-symmetric-kernel-has-two-root-e5-clock
  - relative-pauli-child-split-gives-one-exit-copy
  - corner-localized-non-ce-bcs-energy-gap
---

Because `R_-` is the negative spectral projection of `B`, the complementary
projection `R_+=I-R_-` satisfies `R_+B=R_+`.  Since `AP=-P`,

```text
R_+(BU-UA)P
 = R_+BUP-R_+UAP
 = R_+UP+R_+UP
 = 2R_+UP.                                             (1)
```

Orthogonal compression cannot increase Hilbert--Schmidt norm, so `(1)` gives

```text
4||R_+UP||_2^2 <= ||BU-UA||_2^2.                       (2)
```

Also

```text
||R_+UP||_2^2
 = tau(PU^*R_+UP)
 = tau(P)-tau(R_-UPU^*),                               (3)
```

using `R_++R_-=I`, unitarity, and traciality.  Equations `(2)--(3)` prove
`(HST1)`.

On each forbidden exact packet block, the child-split theorem assigns half of
the forbidden Hilbert mass to a named exit projection on which the aligned
hard commutator is negative.  Summing `(HST1)` over the finitely many
orthogonal atom blocks gives `(HST2)`; bounded overlap changes only the fixed
constant.  Substitute the localized BCS lower bound `(HST3)` to obtain
`(BFE3)` with `eta=beta_B^corner/2`.
