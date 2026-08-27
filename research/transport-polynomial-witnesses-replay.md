---
rg: 2
id: transport-polynomial-witnesses-replay
kind: claim
title: The ghost-doubling and Ledrappier transport identities hold exactly
artifacts:
  - experiments/renormalization_transport_audit.py
distinct_from:
  affine-auxiliary-control-flow-barrier: that is a general finite affine-selector no-go; this records the two exact algebraic transport calculations used to motivate the stable-letter route.
---

Let `S` denote the bilateral shift.  Over `Z/4Z`, the endomorphism

```text
phi=2I+S
```

satisfies

```text
phi^2=4I+4S+S^2=S^2.                                  (TPW1)
```

Thus the apparent ghost-corrected doubling has no iterated decay: after two
steps it is a pure shift.

Over `F_2`, the discrete direct-sum map `psi=I+S` is injective.  Its
Pontryagin-dual map on the full two-shift is surjective with kernel the two
constant configurations.  Explicitly, the equation

```text
y_i=x_i+x_(i-1)                                        (TPW2)
```

has exactly two bilateral solutions, obtained by choosing one seed bit and
recursing in both directions; the two solutions differ by the all-one
configuration.  The replay script verifies every target on a width-nine
window from both boundary seeds.  This finite replay is a check of the local
recurrence, not a claim that the corresponding cyclic finite-window map is
surjective.

