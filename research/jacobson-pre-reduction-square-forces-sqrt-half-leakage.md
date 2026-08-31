---
rg: 2
id: jacobson-pre-reduction-square-forces-sqrt-half-leakage
kind: claim
title: The pre-reduction Jacobson square forces square-root-half leakage but preserves qutrit weights
artifacts:
  - research/jacobson-pre-reduction-square-leakage-proof.md
distinct_from:
  jacobson-residual-t-root-is-orthogonal-transport: that proves the reduced commutator value has zero residual compression; this keeps its T-root and opposite-root constituents separate and quantifies the forced intermediate leakage.
  binary-jacobson-residual-opposite-polar-has-coarse-quarter-gap: that gives a full-polar-or-quarter-boundary dichotomy using only the opposite root and coarse cuts; this uses the alternating relation and improves the unrestricted residual leakage to 1/sqrt(2).
  qutrit-jacobson-residual-has-fixed-polar-gap: that computes the qutrit mass on one residual cut; this audits every intermediate cut of the pre-reduction square and shows the path itself is weight-balanced.
---

Put

```text
e=e_res,       t=x_23(T),       k=x_31(1),
u=[t,k]=t k t k=x_21(T).
```

The root `t` commutes with `e`, while `e u e=0`. Therefore the
separate opposite-root occurrence has the sharp universal lower bound

```text
||(1-e) k e||_op >= 1/sqrt(2).                          (JPS1)
```

In particular, the alternating square cannot be modeled on the residual by
first replacing `k` with a unitary polar entirely inside the `e`-corner.
At least one intermediate `k`-leg has fixed operator-norm mass outside
that corner.

The four constituent transports define

```text
e_0=e,
e_1=k e_0 k,
e_2=t e_1 t,
e_3=k e_2 k,
e_4=t e_3 t=u e u.                                     (JPS2)
```

They satisfy `e_0 e_4=0`. Each `e_j` is a character idempotent of a
conjugate of the order-`2^5` residual group. Consequently, for every
qutrit projection `p in C[F_q]`,

```text
||e_j p||_2^2=tau(p)/32             for 0<=j<=4.        (JPS3)
```

Thus every node of the pre-reduction chain carries the same qutrit masses

```text
q:1/96,                 R:1/144,                 q-R:1/288.
```

The alternating relation forces a genuinely transverse square, not a
weighted Hall deficit. A qutrit contradiction must use an additional
overlap which identifies or deletes one complement branch across these
intermediate cuts. The constituent chain and its forced leakage alone are
exactly weight-balanced.
