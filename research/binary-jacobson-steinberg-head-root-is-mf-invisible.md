---
rg: 2
id: binary-jacobson-steinberg-head-root-is-mf-invisible
kind: claim
title: The Jacobson Steinberg head root dies in every norm-corona representation
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that kills the head root only in exact finite quotients of the elementary group; this asks for operator-norm asymptotic matrix representations of the finitely presented Steinberg cover.
  leavitt-first-offdiagonal-core-is-marked-non-lef: that promotes exact finite-quotient collapse to a fixed finite-table obstruction; this requires a dimension-independent operator-norm robustification of that table.
  toeplitz-defect-needs-square-decoding: that proves the terminal trace inequality after square coefficient operators have been decoded and exhibits rectangular escape otherwise; this is the group-level statement that must rule out that escape.
---

**OPEN.**  Let

```text
J=F_2<S,T | TS=1>,          Gamma_T=St_5(J),
Q=1-ST,                     w_T=x_13(Q).
```

Prove that every homomorphism from `Gamma_T` to a norm matrix corona kills
`w_T`; equivalently

```text
w_T in Rad_MF(Gamma_T).                                  (JMF1)
```

The exact finite analogue is established: `Gamma_T` is finitely presented,
`w_T` is nontrivial, and every homomorphism to a finite group kills it.  The
missing step is operator-norm robustification.  Root commutators encode the
coefficient equations, but arbitrary unitary microstates need not decode
`S,T` as two square matrices on one reservoir.  Rectangular Morita source
and target spaces are the precise surviving escape.

The latest finite-matrix audit does not remove this escape, but it makes the
required certificate explicit.  It is enough to select, separately in each
matrix coordinate and from the surviving head-root microstate, either

1. one nonzero source/target carrier on which the two Toeplitz arrows return
   to the same square reservoir (the operator-norm rank-deficient-return
   endpoint then has gap `1`); or
2. finite-coordinate source and target projections whose authenticated
   transport graph has a uniform weighted Hall deficit (the
   `weighted-unitary-hall-deficit-gap` endpoint then gives a fixed
   normalized-Hilbert--Schmidt defect).

The projections are not allowed to be fixed group-algebra projections.
They must be extracted from the finite matrix coordinate: otherwise the
regular representation would inherit the same certificate.  Thus the
remaining statement is a finite-matrix-only selector/authentication theorem,
not another rank inequality.  The rank, Hall, branching, Atomic Leavitt and
coarse-to-fine leakage endpoints are already terminal once such a selector
has been produced.

A proof of `(JMF1)` would already prove the full binary-Leavitt
Property-`(T)`-free MF-radical theorem.  No classification of the remaining
Leavitt coefficients, diagonal compressors, or invariant measures would be
needed.
