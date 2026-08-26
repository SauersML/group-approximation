---
rg: 2
id: binary-jacobson-raw-cycle-selects-common-pi-intertwiner
kind: claim
title: The Jacobson raw active cycle selects one common sparse PI return
distinct_from:
  binary-jacobson-head-root-has-opnorm-square-decoder: that asks for two same-square Toeplitz coefficient arrows; this asks only for one common intertwiner between the already native degree-two and degree-four Pauli packets.
  binary-jacobson-head-sector-has-native-two-qubit-packet: that proves target fullness and word visibility on the head cut; this asks the raw nonmonomial occurrence to return that tuple to the source factor.
  one-common-intertwiner-carries-the-four-pauli-pi-bridge: that is the analogous abstract affine/Atlas interface on a positive Hilbert--Schmidt carrier; this is the literal binary-Jacobson operator-norm interface and permits an arbitrarily sparse nonzero carrier.
---

**OPEN.**  Use the fixed presentation of

```text
E=EL_3(F_2<S,T | TS=1>)=<a_12,x_12(1),x_23(1),x_31(1)>
```

from `binary-jacobson-active-cycle-generates-rank-three`.  Let
`w=x_13(1-ST)`.  Give a deterministic finite-matrix operation, made from
evaluations of a fixed finite word package, spectral cuts, compression,
polar decomposition and matrix arithmetic, with the following uniform
operator-norm semantics.

Whenever the presentation defect tends to zero and the rounded `w=-1` cut
is nonzero, the operation must output on a nonzero reducing subprojection
`P` of that cut:

* four contractions `C_1,...,C_4` in one exact degree-two source algebra
  `M_2 tensor I`;
* the four corrected literal target words
  `D=(x_12(Q),x_23(1),x_14(Q),x_43(1))|_P`, which generate
  `M_4 tensor I` by
  `binary-jacobson-head-sector-has-native-two-qubit-packet`; and
* one contraction `R in P M_d P` such that

```text
||RR^*-P||_op
  +sum_(j=1)^4 ||D_j R-R C_j||_op <= omega(epsilon),    (JPI1)
```

where `omega(epsilon)->0` independently of the ambient dimension and of
`rank(P)`.

Every output must retain its occurrence type.  In particular `R` must be the
stated compression/polar expression in the **same** raw-cycle word
occurrences used to derive all four rows.  Four unrelated Schur gauges, an
abstract isomorphism of packet representations, or a newly chosen analytic
intertwiner do not satisfy `(JPI1)`.

There is now a canonical degree-two **source candidate**:
`binary-jacobson-head-weyl-cut-is-native-pi-source` canonically cuts the
native two-qubit packet by the negative `x_23(Q)` sign, proves that cut is
nonzero whenever the head survives, and obtains `s_4(C)=0`.  This does not
yet put the source and target on the common carrier demanded by `(JPI1)`.
The open content is precisely to transport that source by the same occurrence
onto a reducing carrier on which the literal target retains degree four.

The first coisometric fold is also explicit.
`binary-jacobson-closing-root-folds-head-two-to-one` combines the balanced
polar with `x_12(1)` and folds the two `x_23(Q)` sign cuts onto one raw range.
The two folded branches agree on three of the four native packet words; their
only relative gauge is the tail-center `x_13(ST)` in the `x_23(1)` row.  The
final opposite-root incidence must control that relative gauge, after which
one still has to authenticate the absolute transported tuple as the literal
native degree-four target.  In particular neither the existence of the source
cut nor the fold alone establishes the common-carrier assertion.

The exact fences make the load-bearing package sharp.  Constant and
`Q`-labelled roots alone lie in the finite marked envelope of
`binary-jacobson-constant-q-root-envelope-is-finite`.  All finitary Clifford
depth and monomial `S/T` transports lie in the amenable marked-MF group of
`binary-jacobson-head-sector-has-native-clifford-tower`.  Every proper part
of the active constant three-cycle remains amenable and marked MF.  Thus the
common return must jointly consume an `S/T`-bearing occurrence and the full
nonmonomial active-cycle incidence.

No carrier-density theorem is requested.  If `(JPI1)` holds on even a
rank-one nonzero `P`, `opnorm-common-intertwiner-pi-gap-is-sparse-terminal`
is already contradictory.

**First polar attempt is exactly calibrated.**  With `u=w_12` and
`h=a_12u`, the involution `h` centralizes the head and fixes the second native
Pauli pair.  `binary-jacobson-naive-head-polar-is-balanced-return` proves

```text
R=P a_12 P=h(PuP),       R^*R=PP',       RR^*=PP'',
```

where `P'` cuts `x_23(Q)` and `P''` cuts the genuinely raw root `x_13(SQ)`.
Thus this is an occurrence-authenticated raw rectangular return, but its two
supports have exactly equal rank.  The desired PI operation must compose it
with further active-cycle incidence that authenticates the four intertwining
rows; this single polar supplies neither a Hall deficit nor unequal PI degree.
