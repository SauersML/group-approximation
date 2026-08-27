---
rg: 2
id: unequal-label-rank-relational-no-go-proof
kind: route
title: Evaluate every relator separately in the label and reservoir tensor factors
target: unequal-label-ranks-forbid-relational-reservoir-conjugacy
requires: []
---

For a reduced word

```text
r=x_(i_1)^(epsilon_1)...x_(i_k)^(epsilon_k),
```

multiplication of elementary tensors gives

```text
r(A tensor V)=r(A) tensor r(V).
```

If the label tuple and the tensor-product tuple both satisfy the relators,
then `I tensor r(V)=I` for every `r in R`, so the reservoir tuple is also a
representation of `P`.  Every equality in `P` therefore holds after
evaluation in either factor.  Evaluating a
conjugacy consequence `x_j=q x_i q^(-1)` gives `(URC3)` in both factors.

Unitary conjugacy preserves spectral multiplicities.  In particular two
self-adjoint involutions with normalized negative ranks `1/4` and `1/8`
cannot be conjugate.  Therefore no exact group-relational cancellation in a
separated tensor packet can deduce the desired reservoir conjugacy across
those two label types.
