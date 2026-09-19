---
rg: 2
id: finite-extraspecial-singer-gauge-proof
kind: route
title: Multiply all outer gauges in the twisted quotient and compare actor support
target: finite-extraspecial-mixed-words-cannot-ungauge-singer-transport
requires:
  - fano-semidir-bridges-are-wrong-subgroup-or-gauged
---

Because `E` is extraspecial, it has a unique irreducible `rho` on which its
center acts by `-1`.  Hence every `J=-1` representation restricts to
`rho tensor I_M`.  For `h in H`, conjugation carries `rho` to an equivalent
representation, so after choosing one spin implementer `U_(hE)`, Schur's
lemma gives uniquely

```text
pi(h)=U_(hE) tensor V_(hE).
```

Multiplication shows that the `V`'s are projective with multiplier inverse
to the spin multiplier.  This proves `(FEM1)` directly.  In particular, if
`w=w_1w_2...w_r`, then the product of the projective reservoir
factors of the occurrences is, up to the inverse spin multiplier already
absorbed by the product of the `U_(w_jE)`, precisely `V_(wE)`.  Thus counting
an even number of outer letters does not imply cancellation; only their
product in `L` matters.

Project the Fourier support of the signed Reynolds source to the actor
quotient.  Conjugation by `e in E` fixes this quotient term by term.  Hence
if `wE=1`, the source support remains `L_0`.  The explicit Singer calculation
in the finite-semidir bridge dichotomy gives

```text
tL_0t^(-1)!=L_0,
```

so every exact support-moving word has `wE!=1`.

Finally, if `V_(wE)` were the identity, or the same fixed
scalar after a fixed change of the label implementer, on every `J=-1`
representation, then the twisted basis element indexed by `wE` would equal
that scalar in the faithful twisted regular representation.  This is
impossible unless `wE=1`.  Therefore some finite marked representation of
the exact packet has a nontrivial quotient gauge.  Since its dimension is
finite, its normalized Hilbert--Schmidt distance from the prescribed scalar
is a fixed positive number, while every packet relator has zero defect.
This proves the claimed exact no-go without importing a general Clifford
classification claim.
