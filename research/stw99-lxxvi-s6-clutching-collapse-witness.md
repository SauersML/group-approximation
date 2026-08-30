---
rg: 2
id: stw99-lxxvi-s6-clutching-collapse-witness
kind: claim
title: A pure coefficient algebra preserves the unstable S6 clutching class until Z-stabilization
artifacts:
  - research/artifacts/stw99-lxxvi-third-depth-audit-2026-08-30.md
---

There exists a unital separable simple pure C*-algebra `D` such that, for the
nonzero unstable clutching class

```text
alpha in pi_5(U(2)) = Z/2,
```

the following hold:

1. `C(S^6) tensor D` is pure;
2. the image of `alpha` in `pi_5(U(M_2(D)))` is nonzero; and
3. its image in `pi_5(U(M_2(D tensor Z)))` is zero.

This remains open.  It is a concrete geometric form of the ideal-local
collapse witness: the associated rank-two projective module is nontrivial
before Z and trivial afterward, although its stable K0 class is already zero.

## Attempts

Taking `D=C` retains the classical unstable bundle but fails pureness because
the fibers are elementary.  Taking `D=Z` makes the continuous field Z-stable
from the outset, so it cannot distinguish the before and after Cu maps.

A natural nonnuclear test coefficient is `D=C*_r(F_2)`: it is simple, pure,
stably finite, and not Z-stable.  Two inputs are not currently established:
pureness of `C(S^6) tensor D`, and the unstable homotopy calculation for

```text
U(2) -> U(M_2(D)) -> U(M_2(D tensor Z)).
```

The recent selfless tensor theorem requires both tensor factors to be
selfless (or the second factor to be simple and uniquely tracial in its cp-map
version); it does not make the commutative-base field pure.  Thus it does not
close either missing input.
