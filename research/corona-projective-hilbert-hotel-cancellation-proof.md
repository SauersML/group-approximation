---
rg: 2
id: corona-projective-hilbert-hotel-cancellation-proof
kind: route
title: Apply the faithful rank-germ dimension to the Leavitt module isomorphism
target: corona-projective-hilbert-hotel-cancellation
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

Write `P=p Q_d^k` and define `Dim_Q(P)=Dim_Q(p)`.  Murray--von Neumann
classification makes this independent of the chosen projection, and block
sum makes it additive.  An isomorphism from `P` to `m` copies of itself gives

```text
Dim_Q(P)=m Dim_Q(P).
```

Eventual coordinate cancellation forces `Dim_Q(P)=0`, and faithfulness gives
`P=0`.

For a binary Leavitt family `s_0,s_1,t_0,t_1`, let `S_i,T_i` be their images
in `End_(Q_d)(P)`.  The maps

```text
S:P directSum P -> P,    S(v_0,v_1)=S_0v_0+S_1v_1,
T:P -> P directSum P,    T(v)=(T_0v,T_1v)
```

are inverse by the Leavitt relations.  Hence `P` is its own double and must
vanish.
