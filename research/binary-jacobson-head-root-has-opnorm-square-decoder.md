---
rg: 2
id: binary-jacobson-head-root-has-opnorm-square-decoder
kind: claim
title: A surviving Jacobson head root selects one square Toeplitz reservoir in each matrix coordinate
distinct_from:
  toeplitz-defect-needs-square-decoding: that establishes the terminal normalized-Hilbert--Schmidt trace payment after a square decoder and exhibits the exact rectangular escape; this asks the group presentation to extract the square decoder in operator norm from a surviving head root.
  opnorm-leavitt-coarse-fine-return-row: that seeks a common carrier for the full binary-Leavitt depth-one/depth-two packets; this is the unary one-branch Jacobson packet and only asks for its two one-sided inverse arrows on one selected corner.
  finite-weyl-root-moments-do-not-authenticate-toeplitz-square: that proves finite Weyl moments and pasted root triangles leave the rectangular Morita model exact; this requires a representation-dependent selector using a full-group incidence outside that interface.
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that gives marked finite partial models for the entire finitary head together with the literal Whitehead shift; this must use relations from the remaining Laurent-symbol elementary quotient.
  binary-jacobson-monomial-symbol-preimage-is-marked-mf: that enlarges the preceding cyclic subsystem to the preimage of every determinant-one monomial Laurent symbol and still retains the mark in an MF model; this must use the interaction with a raw nonmonomial Laurent root.
---

**OPEN.**  Let

```text
J=F_2<S,T | TS=1>,       Gamma_T=St_5(J),
Q=1-ST,                  w_T=x_13(Q).
```

For every sequence of finite-dimensional unitary maps `U_n` with
operator-norm relator defect tending to zero and
`||w_T(U_n)-1||_op` bounded below, select from the individual matrix
coordinate:

* a nonzero projection `C_n` on the surviving spectral cut of the rounded
  head involution;
* a nonzero head projection `P_n<=C_n`; and
* contractions `X_n,Y_n in C_n M_(d_n)(C) C_n`

such that, uniformly in the dimension,

```text
||Y_n X_n-C_n||_op -> 0,
||P_n-(C_n-X_n Y_n)||_op -> 0.                         (JSD1)
```

The selection must be representation-dependent.  A fixed group-algebra
projection or fixed positive-root word cannot do this, because the regular
representation and the established rectangular Morita model satisfy the
same finite group-word interfaces.  The missing input is one authenticated
mixed incidence which erases the source/target object distinction on the
selected coordinate cut.

The finitary head and its literal Whitehead shift still do not suffice:
`binary-jacobson-finitary-whitehead-shift-is-marked-lef` periodizes every
finite inspected window while retaining the head root.  Thus the mixed
incidence required here must use a relation from the full
`EL_5(F_2[z,z^(-1)])` symbol quotient that is absent from that cyclic
subsystem.

The stronger monomial-symbol audit makes the first eligible relation exact.
`binary-jacobson-monomial-symbol-preimage-is-marked-mf` retains the whole
finitary kernel, all balanced Laurent translations and every Weyl
permutation in one marked MF subgroup.  Adjoining any one raw root
`x_ij(S)` or `x_ij(T)` then generates the full elementary group.  Therefore
the decoder must use the interaction of that nonmonomial symbol root with
the monomial preimage; no additional permutation or balanced-shift
incidence can suffice.

Once `(JSD1)` is proved, the sparse operator-norm clause of
`positive-toeplitz-head-is-square-defect-or-rectangular-escape` gives

```text
1 <= o(1)+o(1)/(1-o(1)),
```

a contradiction.  No positive-density bound, trace estimate, property
`(T)`, stability theorem, or branching argument remains after selection.
