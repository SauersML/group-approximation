---
rg: 2
id: robert-selfless-free-product-absorption
kind: claim
title: One selfless factor absorbs every separable faithful-GNS factor under reduced free product
distinct_from:
  stw91-reduced-free-products-preserve-selflessness: that in-repository theorem assumes both factors are selfless but allows both to be nonseparable; Robert's theorem assumes only the first factor is selfless and instead requires the second factor to be separable.
  stw91-anchored-arbitrary-free-products-are-selfless: that iterates this binary theorem and then passes to a directed union over finite subsets.
artifacts:
  - research/artifacts/stw91-anchored-free-product-permanence-audit-2026-08-30.md
---

Let `(A,rho)` be a selfless C*-probability space, and let `(B,tau)` be a
separable C*-probability space whose state has faithful GNS representation.
Then the reduced free product

```text
(A,rho) * (B,tau)
```

is selfless.  No exactness, nuclearity, traciality, or selflessness assumption
is imposed on `B`, and `A` need not be separable.

**Established (literature).**  This is Leonel Robert, *Selfless C*-algebras*,
arXiv:2309.14188v3, Theorem 4.2.  It is imported here with its exact
hypotheses and is not reproved.
