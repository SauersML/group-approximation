---
rg: 2
id: half-period-weyl-band-transport-proof
kind: route
title: Telescope a rectangular intertwiner through the two half-period commutators
target: half-period-weyl-band-transport-is-defect-or-leakage
requires: []
---

For unitaries `A,B,A',B'` and a contraction `W`, put

```text
alpha=||A'W-WA||_2,          beta=||B'W-WB||_2.         (HPT1)
```

The adjoint residuals have the same norms, since

```text
A'^*W-WA^*=-A'^*(A'W-WA)A^*,                           (HPT2)
```

and similarly for `B`. Telescoping the four factors of the commutator gives

```text
||[A',B']W-W[A,B]||_2<=2alpha+2beta.                   (HPT3)
```

Power telescoping also gives

```text
||S^mW-WQ^m||_2<=m delta_Q,
||R^mW-WP^m||_2<=m delta_P.                            (HPT4)
```

Apply `(HPT3)` first to the pairs `(P,Q^m)` and `(R,S^m)`. Because the
initial projection of `W` lies under `E`, `(HPW1)` gives
`W[P,Q^m]=-W`. Therefore

```text
2||((1+C_1)/2)W||_2=||C_1W+W||_2
 <=2 delta_P+2m delta_Q.                               (HPT5)
```

Since `(HPW3)` says `F<=1_(+1)(C_1)`,

```text
||FW||_2<=delta_P+m delta_Q.                           (HPT6)
```

The two row pieces `FW` and `(1-F)W` are orthogonal, so

```text
sqrt(mu)<=||FW||_2+||(1-F)W||_2
        <=delta_P+m delta_Q+sqrt(ell).                 (HPT7)
```

This is the first inequality in `(HPW5)`. Apply the same argument to
`(P^m,Q)` and `(R^m,S)` to obtain the second.

If `ell=0`, add the two inequalities and divide by `m+1` to obtain the
first estimate in `(HPW6)`. The second follows from
`x^2+y^2>=(x+y)^2/2`.
