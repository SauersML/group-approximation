---
rg: 2
id: finite-abelian-same-dimension-rounding-proof
kind: route
title: Repair the flexible Gowers-Hatami representation by an invariant rank projection
target: finite-abelian-hs-almost-actions-round-in-the-same-dimension
requires: []
---

Use the normalized Hilbert--Schmidt stability theorem of Gowers--Hatami
(arXiv:1510.04085v2, Theorem `reppcase` at `p=2`).  For sufficiently small
`epsilon`, it gives

```text
m in [(1-4 epsilon^2)d,(1-4 epsilon^2)^(-1)d],                (1)
rho(x)=V P(x)V^*,                                             (2)
max_x ||f(x)-rho(x)||_(2,d) <= delta:=C_0 epsilon,             (3)
```

where `P:A->U(m)` is exact and `V` is a `d x m` partial unitary.

If `m<=d`, then `E=VV^*` has rank `m`, `(2)` is an exact representation on
`EH`, and extending it by arbitrary one-dimensional characters on
`(1-E)H` changes every matrix by exactly

```text
sqrt((d-m)/d) <= 2 epsilon.                                   (4)
```

This gives `(FA1)` in this case.

Suppose `m>d`.  Now `VV^*=I_d` and `E=V^*V` is a rank-`d` projection in
`C^m`.  Since `rho(x)` is a contraction within `delta` of a unitary,

```text
1-tr_d(rho(x)^*rho(x)) <= 2 delta.                             (5)
```

Indeed, if `s=||rho(x)||_(2,d)<=1`, then
`delta>=1-s`, and `1-s^2<=(1+s)delta`.
Using `(2)`, equation `(5)` gives

```text
||E-P(x)^* E P(x)||_(2,m)^2 <= 4 delta.                        (6)
```

Average the conjugates:

```text
B=E_x P(x)^* E P(x).
```

This is the trace-preserving conditional expectation of `E` onto the
commutant of `P(A)`.  Orthogonality of conditional expectation and `(6)`
give

```text
||E-B||_(2,m)^2 <= 2 delta.                                   (7)
```

Because `A` is abelian, `P` is a direct sum of one-dimensional characters.
Choose, within the simultaneous character decomposition, the spectral
projection `F` of `B` onto its `d` largest eigenvalues.  It commutes with
`P(A)`, has rank `d`, and the Eckart--Young variational principle gives

```text
||B-F||_(2,m) <= ||B-E||_(2,m).                               (8)
```

Thus `||E-F||_(2,m)<=2 sqrt(2 delta)`.  Equal-rank projections admit a
principal-angle unitary `S` with

```text
S E S^*=F,
||S-I||_(2,m) <= sqrt(2)||E-F||_(2,m).                         (9)
```

Since `F` commutes with `P(A)`, the matrices

```text
pi(x)=V S^* P(x) S V^*
```

form an exact `d`-dimensional representation.  Two telescoping terms in
`S^*P(x)S-P(x)`, followed by compression with `V`, show

```text
||pi(x)-rho(x)||_(2,d)
 <= 2 sqrt(m/d) ||S-I||_(2,m)
 <= C_1 sqrt(delta).                                          (10)
```

The ratio `m/d` is universally bounded by `(1)`.  Combine `(3)` and `(10)`
and absorb the linear term into `C sqrt(epsilon)`.  This proves `(FA1)`.

