---
rg: 2
id: binary-tracial-two-csp-classical-proof
kind: route
title: Read forbidden Boolean pairs as operator implications and apply the 2-SAT criterion
target: binary-tracial-two-csp-has-classical-solution
requires: []
---

For a Boolean literal `ell=(x=a)`, write

```text
E_ell=P_x^a,             E_(not ell)=P_x^(1-a).          (BTC1)
```

A forbidden pair `(x=a,y=b)` is the 2-CNF clause

```text
not (x=a) or not (y=b).                                  (BTC2)
```

Its operator relation is

```text
E_(x=a) E_(y=b)=0.                                       (BTC3)
```

The two endpoint projections commute.  Hence `(BTC3)` is equivalent to both
projection-order implications

```text
E_(x=a) <= E_(y=1-b),
E_(y=b) <= E_(x=1-a).                                    (BTC4)
```

These are exactly the two arrows contributed by `(BTC2)` to the ordinary
2-SAT implication graph.  A forbidden unary value gives `E_(x=a)=0`, or
equivalently pins the complementary literal to one.

If the resulting Boolean 2-CNF were unsatisfiable, the implication-graph
criterion would give a literal `ell` for which there are directed paths

```text
ell -> not ell,             not ell -> ell.              (BTC5)
```

Projection order is transitive.  Composing `(BTC4)` along the two paths gives

```text
E_ell <= E_(not ell) <= E_ell,
```

so `E_ell=E_(not ell)`.  But the two projections in `(BTC1)` are orthogonal
and sum to one.  Equality would force both to be zero and their sum to be
zero, a contradiction.  Therefore the 2-CNF is satisfiable, and any satisfying
Boolean assignment lies in every original unary or binary relation.

For the tracial-correlation formulation, let `P,Q` be the commuting endpoint
projections of a forbidden atom.  Perfect loss gives

```text
tau(PQ)=0.
```

Since `PQ` is a projection, its image is zero after quotienting by the trace
kernel and passing to the faithful GNS support.  The preceding operator-order
argument then applies verbatim.  The resulting deterministic assignment is a
one-dimensional perfect strategy.
