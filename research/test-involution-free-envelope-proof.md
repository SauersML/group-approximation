---
rg: 2
id: test-involution-free-envelope-proof
kind: route
title: Symmetrize the artificial test involution and freely extend the resulting ucp maps
target: test-involution-pays-free-envelope-gap
requires: []
---

Put

```text
A=(B+B^*)/2.
```

This is a self-adjoint contraction.  Hence the assignments

```text
(1+r)/2 -> (I+A)/2,
(1-r)/2 -> (I-A)/2
```

define a ucp map `Phi_1:C^*(C_2)->M_d` with `Phi_1(r)=A`.  For every
free cyclic factor, use the representation `Phi_j(u_j)=X_j`.  The standard
unital free-product extension of ucp maps gives

```text
Phi:C^*(C_2*F_(m-1))->M_d
```

whose values on the displayed generators are `(A,X_2,...,X_m)`.
Therefore the support function at `C` is at least its value on this tuple.
The source pairing is `sqrt(m)`, while

```text
Re tr(B^*A)
 =Re tr((I+B^(*2))/2)
 =(1+Re tr(B^2))/2.                                  (RIP1)
```

It follows that

```text
Delta(C;x)
 <=(1-Re tr(B^*A))/sqrt(m)
 =(1-Re tr(B^2))/(2 sqrt(m))
 =||B^2-I||_2^2/(4 sqrt(m)),                          (RIP2)
```

which is `(RIG1)`.  If `B^2=-I`, the last quantity is `1/sqrt(m)`;
the support calculation in the cited countermodel attains it.

This proof concerns the deliberately chosen envelope
`C^*(C_2*F_(m-1))`.  It does not impose a genuine relation of
`SL_3(Z)`: the elementary root element represented by `B` in the intended
arithmetic problem has infinite order.  Thus the ucp symmetrization closes
only the artificial order-two test gap and leaves the mixed arithmetic
matrix-range problem untouched.
