---
rg: 2
id: block-transport-cluster-unitarization-proof
kind: route
title: Truncate cross-component blocks, balance dimensions, and take polar factors
target: block-transport-cluster-unitarization
requires: []
---

Write normalized Hilbert--Schmidt norm as `||T||_2^2=Tr(T*T)/d`, always
normalized by the original dimension.  For a graph component `C`, set

```text
V_C=P_C U Q_C,
out_C=||(1-P_C)UQ_C||_2^2,
in_C =||P_C U(1-Q_C)||_2^2.
```

Every block counted by `out_C` or `in_C` joins different graph components,
so

```text
sum_C out_C = sum_C in_C = gamma.                     (1)
```

Also

```text
tau(Q_C)=||V_C||_2^2+out_C,
tau(P_C)=||V_C||_2^2+in_C.                            (2)
```

Hence

```text
|rank(P_C)-rank(Q_C)|/d <= in_C+out_C.                (3)
```

Because the total source and target dimensions are both `d`, the positive
and negative dimension imbalances sum to the same integer `r`.  Summing `(3)`
gives

```text
2r/d <= 2 gamma,       so r/d <= gamma.               (4)
```

For each component, pad only its smaller side by the exact dimension
difference, using a trivial representation there.  Globally this adds exactly
`r` dimensions to each side and makes the source and target dimensions equal
component by component.

Extend `V_C` by zero on the new coordinates; call the resulting square
component operator `V~_C`.  It is a contraction.  Choose a singular-value
decomposition and replace every singular value by `1`; this gives a unitary
`W_C` on the stabilized component.  If the target component was the larger
one, then

```text
sum_k (1-s_k(V~_C)^2)
 = rank(P_C)-Tr(V_C V_C*)
 = d in_C.
```

If the source was larger, the same expression is `d out_C`.  Since
`0<=s<=1` implies `(1-s)^2 <= 1-s^2`,

```text
||W_C-V~_C||_2^2 <= in_C+out_C.                       (5)
```

Summing and using `(1)` yields

```text
||W-V~||_2 <= sqrt(2 gamma).                           (6)
```

Let `U_0` denote `U` on the original coordinates and zero on the padding.
Orthogonality of the matrix blocks gives exactly

```text
||U_0-V~||_2^2
 = sum_(C != C') ||P_C U Q_(C')||_2^2
 = gamma.                                              (7)
```

The triangle inequality in `(6)--(7)` proves `(BCU1)`.

For the intertwining estimate, sums of reducing projections still reduce the
representations, so for every `s`

```text
rho(s)V_C-V_C sigma(s)
 = P_C (rho(s)U-U sigma(s)) Q_C.
```

The component compressions are Hilbert--Schmidt orthogonal.  Therefore, after
zero extension to the padding,

```text
sum_s ||rho~(s)V~-V~sigma~(s)||_2^2 <= E(U).           (8)
```

For any two unitaries `R,S` and any `X`,

```text
||R X-X S||_2 <= 2||X||_2.
```

Apply this to `X=W-V~`, square-sum over `s`, and use Minkowski in the direct
sum over `S`:

```text
sqrt(E(W))
 <= sqrt(E(V~))+2 sqrt(|S|)||W-V~||_2
 <= sqrt(E(U))+2 sqrt(2 |S| gamma).                    (9)
```

This is `(BCU2)`.  The construction is performed independently on graph
components, so `W` has no cross-component matrix blocks.  Equation `(4)`
proves the stabilization bound and completes the proof.