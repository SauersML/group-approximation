---
rg: 2
id: paz-vector-graph-dimension-loss-proof
kind: route
title: Compute the exact adjoint-dimension loss in the PAZ vector graph
target: paz-gram-vector-is-not-a-graph-projection
requires: []
---

# Direct proof

Let `K` have dimension `N`, let `xi` be a unit vector, put

```text
e=|xi><xi|,
eta_vec=1-Re <xi,Wxi>,
b_vec=||(I-e)Wxi||^2,
```

and let `W` be unitary. Perform the two fixed graph amplifications from
`graph-commutator-authenticates-paz-return`, now honestly in `End(K)` with
its normalized trace. If `C` is the resulting commutator of involutions,
then the graph calculation is supported on the line `eK`. Its ordinary
trace defect is

```text
2 eta_vec+b_vec.
```

Normalized trace on `End(K)` divides this by `N`, so exactly

```text
||C-I||_2^2=(2 eta_vec+b_vec)/N.                         (PVG1)
```

Moreover

```text
b_vec=1-|<xi,Wxi>|^2
     <=2(1-Re <xi,Wxi>)=2 eta_vec,                       (PVG2)
```

and hence

```text
2 eta_vec/N <= ||C-I||_2^2 <= 4 eta_vec/N.               (PVG3)
```

The fixed `2 by 2` amplifications preserve this factor: they multiply the
relevant rank and ambient operator dimension by the same constant. In PAZ,
`K=L^2(M_d,tr_d)` up to a fixed control factor, so `N` grows as `d^2`.

## Sharp exact family

For sharpness take `K=L^2(M_d,tr_d)`, `xi=I_d`, and `W=L_Z` for a traceless
self-adjoint involution

```text
Z=diag(I_(d/2),-I_(d/2)).
```

This is an exact left-multiplication superoperator of the same left--right
type as the PAZ Gram return. Then

```text
<xi,Wxi>=tr_d(Z)=0,
eta_vec=1,
eWe=0,
b_vec=1.
```

Thus the strict-compression hypothesis used by GIF holds with `rho=0`, yet

```text
||C-I||_2^2=3/d^2.                                      (PVG4)
```

Taking the proposed authenticated involution `Y=I` gives exact involutivity
and mixed defect `3/d^2 -> 0`, while the PAZ vector loss stays one. Therefore
no dimension-independent constant `K` can satisfy

```text
eta_vec <= K( ||C-Y||_2^2 + ||Y^2-I||_2^2 ).            (PVG5)
```

This identifies the precise failure in GIF: the exact two-projection theorem
is valid for a genuine projection in a finite tracial algebra, but the honest
projection supplied by one PAZ vector has normalized trace `1/N`, not the
vector mass. Exact zero-defect collapse does not provide a uniform
normalized-HS modulus.

## Boundary of the result

This finite family refutes the analytic promotion from the stated PAZ data;
it need not realize the full game packet. A repair would have to prove new
module coherence: replace the rank-one line by a `W_game`-coherent subspace
of rank comparable to `N||P_0Q||_2^2`, for example a controlled form of
`QM_d`. PAZ currently controls only the vector `P_0Q`.

The correctly typed surviving identity is therefore

```text
2 eta_0(Q)=||(W_game-I)P_0Q||_2^2,
```

from `acceptance-return-is-one-corner-word`, rather than a positive-density
operator graph.
