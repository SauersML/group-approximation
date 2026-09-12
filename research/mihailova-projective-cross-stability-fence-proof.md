---
rg: 2
id: mihailova-projective-cross-stability-fence-proof
kind: route
title: Separate commuting and projectively commuting lifts and insert the Weyl packet
target: mihailova-free-rounding-projective-cross-fence
requires: []
---

There are no relations internal to either displayed free generating tuple,
so factorwise exactification changes nothing: the cross commutators are the
whole presentation defect.  Adrian Ioana,
[*Almost commuting matrices and stability for product groups*](https://arxiv.org/abs/2108.09589),
Theorem B, proves that `F_m x F_k` is not HS-stable for `m,k>=2`; Lemma 2.6
in the same paper identifies flexible and same-dimensional stability here.
This proves the ordinary-lift obstruction.

For the projective boundary, on the standard basis `e_r`, indexed modulo
`d`, define

```text
S_d e_r=e_(r+1),             D_d e_r=zeta_d^r e_r.
```

Direct calculation gives `D_d S_d=zeta_d S_d D_d`.  The group commutator is
therefore the scalar `zeta_d 1`, proving `(MPS3)` and `(MPS4)`.  Its defect
is `|zeta_d-1|`, independent of normalization, and tends to zero although
the packet has trace one as a projection.

Finally, under the standard identification
`L^2(M_d)=C^d tensor conjugate(C^d)`, `Ad(W)=W tensor conjugate(W)`.  Therefore

```text
tr_(d^2)(Ad(W))=|tr_d(W)|^2
```

and the unitary distance formula gives `(MPS5)`.  Thus the adjoints of any
Mihailova actor microstate are approximate ordinary representations, while
the Weyl packet proves that an exact adjoint representation corresponds only
to a projective, not necessarily ordinary, matrix lift.
