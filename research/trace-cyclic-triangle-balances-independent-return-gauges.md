---
rg: 2
id: trace-cyclic-triangle-balances-independent-return-gauges
kind: claim
title: A third cyclic edge balances two independent proper-return gauge layers
distinct_from:
  two-oriented-trace-cyclic-returns-cancel-the-gauge: that assumes the two returns use one common hidden projection; this needs only equality of the two hidden normalized ranks and obtains it from a third cyclic pair.
  fanizza-product-gram-reduces-to-one-state-holonomy: that isolates one operator-valued chord holonomy after rooting the incidence graph; this shows that the scalar rank ledger needs no operator-valued holonomy alignment.
  single-triangle-trace-cyclic-return-cell: that originally asks for one source-to-prescribed-target return; this supplies a three-edge scalar endpoint shaped exactly like the native triangle.
---

Let `E,H,G_0,G_1 in M_d(C)` be projections with

```text
G_0<=H<=E,                 G_1<=H<=E.                  (TCT1)
```

Suppose two oriented return pairs obey

```text
|tr(Y_0X_0)-tr(E)|
 +|tr(X_0Y_0)-tr(E-H+G_0)| <= epsilon_0,               (TCT2)

|tr(Y_1X_1)-tr(E)|
 +|tr(X_1Y_1)-tr(E-G_1)|   <= epsilon_1,               (TCT3)
```

and a third pair of arbitrary matrices balances the two hidden gauges:

```text
|tr(BA)-tr(G_0)|+|tr(AB)-tr(G_1)| <= epsilon_b.        (TCT4)
```

Then

```text
tr(H)<=epsilon_0+epsilon_1+epsilon_b.                  (TCT5)
```

No common coordinate system, common projection, or approximate conjugacy
between `G_0` and `G_1` is required.  The third edge uses only equality of
their normalized ranks, and finite-dimensional cyclicity supplies that
equality automatically from `(TCT4)`.

This is the scalar form of a two-matching/nonflat triangle actuator.  The two
return orientations may carry completely independent stationary
multiplicity gauges; one ordinary rank-balancing chord closes the ledger.
Unlike the proper returns `(TCT2)--(TCT3)`, the balance edge `(TCT4)` may be
tracially functorial without violating the regular firewall: by itself it
only asserts `tr(G_0)=tr(G_1)` and pays no positive projection.

For the native Fanizza triangle this gives a concrete division of labor:

1. the two tree orientations need only decode complementary *forms* of the
   one-sided return, with unrelated leakage projections `G_0,G_1`;
2. the last chord need only balance their ranks through one cyclic block
   pair; and
3. the three scalar cyclicities, not a globally aligned chord observable,
   pay the whole D8 projection `H`.

Thus the still-open word/corner theorem can be weaker than `(STR1)`: it need
not reconstruct one holonomy projection on all three contexts.  It must
construct the two finite-matrix-only proper returns and one same-occurrence
rank-balancing block pair.

