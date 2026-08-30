---
rg: 2
id: stw83-circle-circle-boundary-index-proof
kind: route
title: Compute the Busby index from the defect of the upstream cycle lift
target: stw83-circle-circle-boundary-index
requires: []
---

## Identify the extension

The direction hypothesis makes `H=V_1 union V_2` hereditary.  It is
saturated because every vertex of `V_0` emits its cycle edge back into `V_0`,
so no such vertex can be added by saturation.  The standard gauge-invariant
ideal sequence is therefore

```text
0 -> I_H -> C*(F) -> C*(F minus H) -> 0.                (4)
```

The quotient graph is the simple cycle on `V_0`, giving (1).  In the graph on
`H`, the downstream cycle projection is full: order the acyclic vertices of
`V_1` backwards from `V_2` and use the Cuntz--Krieger equality at each vertex.
Its corner is the matrix circle algebra of the simple cycle on `V_2`.
The standard full-corner description of a gauge-invariant graph ideal then
shows that `I_H` is Morita equivalent to `C(T)`.  In particular

```text
K_0(I_H)=Z[p_w]                         (w in V_2),     (5)
```

and all downstream cycle vertex projections have the same class.

The same backwards induction computes every connector vertex class.  For
`v in V_1`, the graph is finite and `v` is not a sink because it reaches
`V_2`; hence

```text
[p_v]=sum_{e:s(e)=v}[s_e s_e*]
     =sum_{e:s(e)=v}[p_{r(e)}]
     =n(v)[p_w].                                         (6)
```

The recursion terminates because `V_1` is acyclic.

## Compute the index

Let `P_0=sum_{v in V_0}p_v`, let `C_0^1` be the cycle edges in `V_0`, and put

```text
S=sum_{a in C_0^1}s_a,
D=sum_{e:s(e) in V_0, r(e) in H}s_e s_e*.
```

The Cuntz--Krieger relations and orthogonality of distinct edge ranges give

```text
S*S=P_0,                    SS*=P_0-D.                  (7)
```

Modulo `I_H`, the element `S` is the standard cycle unitary in
`M_|V_0|(C(T))`; its determinant winds once and hence its `K_1` class is the
chosen generator.  The partial-isometry formula for the six-term index map,
applied in the corner with unit lift `P_0`, gives

```text
partial_1([S mod I_H])
  =[P_0-S*S]-[P_0-SS*]
  =-[D].                                                (8)
```

Each summand `s_e s_e*` of `D` is Murray--von Neumann equivalent inside the
ideal to `p_{r(e)}`.  Equations (2), (5), and (6) therefore give

```text
[D]=sum_e n(r(e))[p_w]=N[p_w],                         (9)
```

which proves (3).  Every `n(v)` is positive and there is at least one exit
from `V_0`, so `N>=1`.  Reversing the `K_1` generator or using the opposite
standard convention for the connecting map reverses the sign in (8), but not
the nonzero index or any consequence below.

## Consequences for the frontier

A split extension has zero connecting maps, so (3) rules out splitting.  It
also rules out a quasicentral approximate unit of projections for `I_H`.
Indeed, suppose `(q_k)` were such an approximate unit and `u` were a quotient
unitary with lift `x`.  In a matrix amplification, quasicentrality and the
approximate-unit property make

```text
y_k=(1-q_k)x(1-q_k)
```

arbitrarily close to a unitary in the corner `(1-q_k)C*(F)(1-q_k)`, while
`y_k` still maps to `u`.  For large `k`, polar correction in that corner
produces an actual unitary lift of `u`, forcing `partial_1([u])=0`.  This
contradicts (3) for the cycle generator.  This is precisely the projection
orthogonality mechanism used by quasidiagonal-extension color reuse, so that
mechanism is unavailable here.

Finally (7) exhibits `S` as a partial isometry from `P_0` onto the proper
subprojection `P_0-D`; the defect is nonzero because graph edge partial
isometries are nonzero.  Hence `P_0` is infinite.  This independently confirms
that the middle algebra is not stably finite and that the existing
stably-finite graph theorem cannot cover these examples.  No nuclear-dimension
value is inferred from the nonzero index: the dimension-one question for this
family remains open.
