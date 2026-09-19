---
rg: 2
id: nested-conjugacy-bcs-embedding-has-quadratic-depth-loss
kind: claim
title: Nested-conjugacy BCS relations flatten with quadratic depth loss and trace extension
artifacts:
  - research/artifacts/fanizza-npa-ingestion-delta-2026-08-20.md
distinct_from:
  fanizza-final-bcs-has-fixed-nonlinear-menu: that audits the particular predicate shapes left in the Fanizza machine; this is the general quantitative embedding theorem for every finite nested-conjugacy BCS.
  fanizza-bcs-polynomial-doubling-tape: that applies the embedding inside one machine construction; this records the compiler interface and its exact loss independently of the tape.
---

Let `B=(W,{C_i})` be a finite Boolean constraint system whose variables are
nested-conjugacy variables over a Boolean set `X`, all of depth at most
`ell>=1`.  If `M=max_i |U_i|` is the largest context size, then one can
effectively construct an ordinary finite BCS `B_tilde` such that:

1. the natural map on the original variables descends to an embedding

```text
A_nest^X(B) -> A(B_tilde);                                      (NCB1)
```

2. every tracial state on `A_nest^X(B)` extends to a tracial state on
   `A(B_tilde)`; and
3. if a polynomial `beta` over `X` has a nested-relator decomposition of
   size `Lambda`, then it has an ordinary BCS-relator decomposition of size

```text
at most 2^16 M^2 ell^2 Lambda.                                  (NCB2)
```

The proof first adjoins a variable for every successive conjugate.  This
flat stage costs at most `9 M^2 ell^2`.  Each remaining relation
`x_1 x_2 x_1=x_3` is then replaced by a fixed linear-BCS gadget: 42 Boolean
variables, 31 linear constraints of context size at most three, and
relator-decomposition cost at most `1750`.  The trace-extension statement is
part of both stages, so `(NCB1)` does not merely preserve algebraic
nonzeroness.
