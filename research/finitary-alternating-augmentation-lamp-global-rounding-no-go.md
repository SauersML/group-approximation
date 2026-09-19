---
rg: 2
id: finitary-alternating-augmentation-lamp-global-rounding-no-go
kind: claim
title: Highly transitive augmentation lamps have no uniform global semidirect PVM rounding
distinct_from:
  hyperlinearity-cannot-see-the-lamp-module: that is a von Neumann invariance warning for two different module structures; this is one explicit locally finite group whose microstates cannot be globally exactified while preserving a lamp.
  same-basis-rounding-interface-for-sparse-weyl-sampler: that asks only for a finite F_2^n occurrence table; this rules out a stronger all-sites semidirect exactification for one infinite augmentation module.
---

ESTABLISHED.  Let `X` be countably infinite,

```text
A=Alt_fin(X),
M={f in direct_sum_X F_2 : sum_x f(x)=0},
Gamma=M rtimes A.                                              (FAN1)
```

Then:

1. `A` is simple and highly transitive; its diagonal action on every fixed
   `X^r` has only the finitely many equality-pattern orbits.
2. `Gamma` is locally finite, hence amenable, sofic, and hyperlinear.
3. Every finite-dimensional unitary representation of `Gamma` kills `M`.

Consequently there is no dimension-independent decoder which takes every
sufficiently accurate matrix model of the semidirect relations to an exact
finite-dimensional representation of the **whole** module/actor pair while
remaining `o(1)`-close on one fixed nonzero lamp `m in M`.  Canonical
microstates of the locally finite group are an explicit counterexample: they
separate `m`, whereas every exact decoded representation kills it.

This proves that high transitivity, finitely many bounded-tuple orbit types,
and exact point-lamp involution/commutation laws do not by themselves give
the global PVM decoder needed by the infinite-character route.  A positive
result for a finitely presented property-`(T)` actor must use its quantitative
spectral rigidity, not merely the finite orbit combinatorics.

