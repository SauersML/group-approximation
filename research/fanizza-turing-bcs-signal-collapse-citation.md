---
rg: 2
id: fanizza-turing-bcs-signal-collapse-citation
kind: route
title: Import the L-family theorem and its polynomial computation recurrence
target: fanizza-turing-bcs-signal-collapse
requires:
  - fanizza-bcs-polynomial-doubling-tape
  - near-perfect-bcs-strategy-gives-synchronous-relator-state
artifacts:
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
---

**Established by citation.**  Marco Fanizza, Larissa Kroell, Arthur Mehta,
Connor Paddock, Denis Rochette, William Slofstra, and Yuming Zhao, *The NPA
hierarchy does not always attain the commuting operator value*,
arXiv:2510.04943 (2025).

Definition 4.1 defines an `L`-family with exactly the two alternatives in the
claim, including `D=(1-x_D)/2` and `phi(D)<=C_m epsilon`.  Theorem 4.4 proves
that an `L`-family exists for every RE set.  Proposition 5.14 proves the
displayed level-`n` computation relation and a polynomial-size decomposition
in the finite BCS relator ideal.  The proof of Theorem 4.4 then sums those
estimates with exponentially decaying weights and obtains `(FTB1)`.

The source was checked against arXiv version 2510.04943 on 2026-08-20.  The
paper does not state a fixed-`lambda` scalar recurrence of the form
`a_n<=lambda a_(n+1)+poly(n)sqrt(E)`; what it establishes is the polynomial
decomposition plus the final signal estimate above.  No stronger recurrence
is imported here.
