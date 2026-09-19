---
rg: 2
id: amenable-crossed-products-preserve-invariant-amenable-traces
kind: claim
title: Countable amenable crossed products preserve invariant amenable traces
distinct_from:
  stw10-finite-crossed-products-preserve-amenable-and-qd-traces: that theorem treats finite acting groups and preserves both amenability and quasidiagonality; this treats every countable amenable acting group but only amenability, and the quasidiagonal analogue is false.
  amenable-action-invariant-trace-forces-amenability: that concerns amenable actions on nuclear algebras and deduces amenability of the acting group; this starts with an amenable acting group and transports one amenable trace, with no nuclearity or action-amenability assumption.
artifacts:
  - research/artifacts/amenable-crossed-product-trace-dichotomy-2026-08-30.md
---

Let `A` be a separable unital C-star algebra, let a countable amenable group
`Q` act by `alpha:Q->Aut(A)`, and let `tau` be an `alpha`-invariant
amenable trace on `A`.  On the maximal crossed product put

```text
B=A rtimes_(alpha,max) Q,
sigma=tau compose E,
```

where `E` is the coefficient expectation obtained through the regular
quotient.  Then `sigma` is an amenable trace.

No exactness, nuclearity, UCT, residual finiteness, or lifting property is
assumed.  The result is deliberately not stated for quasidiagonal traces:
`integer-crossed-products-can-destroy-quasidiagonal-traces` gives a
counterexample already for `Q=Z`.
