---
rg: 2
id: binary-jacobson-steinberg-head-root-is-mf-invisible
kind: claim
title: The Jacobson Steinberg head root dies in every norm-corona representation
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that kills the head root only in exact finite quotients of the elementary group; this asks for operator-norm asymptotic matrix representations of the finitely presented Steinberg cover.
  leavitt-first-offdiagonal-core-is-marked-non-lef: that promotes exact finite-quotient collapse to a fixed finite-table obstruction; this requires a dimension-independent operator-norm robustification of that table.
  toeplitz-defect-needs-square-decoding: that proves the terminal trace inequality after square coefficient operators have been decoded and exhibits rectangular escape otherwise; this is the group-level statement that must rule out that escape.
  binary-jacobson-mf-radical-dichotomy: that proves the elementary group is MF or has exactly the finitary symbol kernel as radical; this asks which side of that exact dichotomy occurs.
---

**ESTABLISHED (2026-09-08, mathematical proof using property (T)).** Let

```text
J=F_2<S,T | TS=1>,          Gamma_T=St_5(J),
Q=1-ST,                     w_T=x_13(Q).
```

Every homomorphism from `Gamma_T` to a norm matrix corona kills
`w_T`; equivalently

```text
w_T in Rad_MF(Gamma_T).                                  (JMF1)
```

The route `jacobson-head-collapses-by-rank-weighted-transport` proves
this using uniformly bounded finite-subgroup active ranks and positive
cutoffs in rescaled Hilbert spaces. Together with the radical dichotomy,
it gives `Rad_MF(Gamma_T)=L`, the finitary symbol kernel. No Lean
certification of this new proof is asserted.

## Previous reductions and attempts

The paragraphs below describe the former alternatives and decoder
approaches. The rank-weighted proof settles the ordinary mathematical
claim through a different mechanism; the property-(T)-free proof
obligation is now `property-t-free-jacobson-head-collapse`.

There is no longer a cover ambiguity.  By
`binary-jacobson-steinberg-cover-is-elementary`, `Gamma_T=EL_5(J)`.  By
`binary-jacobson-head-retaining-homomorphisms-are-faithful`, every
homomorphism retaining `w_T` is faithful.  Thus `(JMF1)` is equivalent to
saying that this one explicit group is not operator-MF.  The radical
dichotomy says its only alternatives are

```text
Rad_MF(Gamma_T)=1       or       Rad_MF(Gamma_T)=L,      (JMF2)
```

where `L` is the finitary simple kernel and contains `w_T`.

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

A proof of `(JMF1)` **without property (T)** would prove the full binary-Leavitt
Property-`(T)`-free MF-radical theorem. The weighted proof uses property (T)
and does not supply that conclusion. No classification of the remaining
Leavitt coefficients, diagonal compressors, or invariant measures would be
needed.
