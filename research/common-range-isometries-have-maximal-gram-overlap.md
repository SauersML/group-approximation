---
rg: 2
id: common-range-isometries-have-maximal-gram-overlap
kind: claim
title: Partial isometries onto one common range have maximal cross-Gram mass
---

Let `(M,tau)` be a finite tracial von Neumann algebra and let `S,T in M` be
partial isometries with the same final projection

```text
S S^* = T T^* = E.
```

Then the cross-Gram operator has exactly the mass of the common range:

```text
||S^* T||_2^2 = tau(E).
```

Equivalently, two isometric branches which are both onto the same positive-
trace target can never satisfy an `o(1)` incoming Gram-overlap requirement.
This is independent of the initial projections and of the formulas producing
the two branches.