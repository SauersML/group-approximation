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
artifacts:
  - research/artifacts/locally-finite-dimensional-compression-2026-09-07.md
---

Let

    J=F_2<S,T | TS=1>,          Gamma_T=St_5(J),
    Q=1-ST,                     w_T=x_13(Q).

Every homomorphism from Gamma_T to a norm matrix corona kills w_T.
Equivalently,

    w_T in Rad_MF(Gamma_T).                                  (JMF1)

The route binary-jacobson-mf-collapse-proof proves this using the
locally finite-dimensional orbit theorem. In EL_4(J), the subgroup
EL_3(J) has property (T), the compression cell conjugates a centralizing
element to e_12(Q), and its commutator with e_23(1) is e_13(Q).
The L-conjugacy orbit lies in the locally finite congruence kernel
associated to JQJ, so semisimple-packet collapse applies. Restriction
from rank five and the established isomorphism

    St_5(J) ~= EL_5(J)

give the stated Steinberg endpoint.

More precisely, the complete proof computes

    Rad_MF(Gamma_T)=L,                                       (JMF2)

where L is the finitary general linear symbol kernel. Its elementary
transvections are conjugates of the head root, while the Laurent
elementary quotient is residually finite. This selects the nontrivial
branch of binary-jacobson-mf-radical-dichotomy and identifies the
universal MF quotient with EL_5(F_2[z,z^(-1)]).

Earlier approaches sought a square Toeplitz decoder or a finite-coordinate
Hall deficit. The orbit proof works directly with finite-dimensional
group-algebra windows of the finitary kernel. It uses property (T)
of EL_3(J); it does not construct such a decoder or a Hall selector,
and it does not provide a hyperlinear obstruction.

## Proof status

The artifact contains a complete written proof in every elementary
rank n>=4. The transfer to the rank-five Steinberg group uses the
existing claim binary-jacobson-steinberg-cover-is-elementary.
The new analytic and ring endpoints have not been formalized in Lean.
