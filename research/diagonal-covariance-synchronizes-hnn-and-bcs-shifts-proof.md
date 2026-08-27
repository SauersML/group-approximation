---
rg: 2
id: diagonal-covariance-synchronizes-hnn-and-bcs-shifts-proof
kind: route
title: Centralize the difference shift and use a tensor-product marked model
target: diagonal-covariance-synchronizes-hnn-and-bcs-shifts
requires:
  - ascending-hnn-shift-cannot-be-an-involution-product
---

From `[t,U]=1` and `[tU^(-1),z]=1`,

```text
t U^(-1) z U t^(-1)=z
```

becomes `U^(-1)tzt^(-1)U=z`, hence `tzt^(-1)=UzU^(-1)`.
Iteration proves `(DC2)`. Both commutators in `(DC1)` have height zero, so
the original height map extends.

For the exact model, the displayed tensor assignments satisfy the HNN
relations because the BCS tensor factor cancels when conjugating a Toeplitz
base element. They satisfy `(DC1)` because

```text
pi(t U^(-1))=pi_T(t) tensor I,
```

which commutes with the entire BCS tensor factor. A word contained in that
factor has exactly its original operator value, proving marked completeness.

