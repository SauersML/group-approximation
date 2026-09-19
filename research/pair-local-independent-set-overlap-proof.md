---
rg: 2
id: pair-local-independent-set-overlap-proof
kind: route
title: Specialize the partial-isometry swap to one forbidden row projection
target: pair-local-independent-set-overlaps-need-no-common-gram
requires:
  - synchronous-independent-set-reduction-preserves-a-quadratic-gap
  - partial-isometry-swap-wordizes-one-bcs-gram-row
---

For one forbidden pair set `S=P_j^v`, `A=1-2P_i^u`, and `B=1`.  Then

```text
AS-SB=-2P_i^uP_j^v.
```

Substitution in `(PIS6)` gives `(PLO1)`.  Since every such overlap belongs
to the same already authenticated PVM family, no cross-row Gram alignment
is needed.

