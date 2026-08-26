---
rg: 2
id: binary-jacobson-raw-cycle-selects-common-pi-intertwiner
kind: claim
title: The Jacobson raw active cycle selects one common sparse PI return
distinct_from:
  binary-jacobson-head-root-has-opnorm-square-decoder: that asks for two same-square Toeplitz coefficient arrows; this asks only for one common intertwiner between the already native degree-two and degree-four Pauli packets.
  binary-jacobson-head-sector-has-native-two-qubit-packet: that proves target fullness and word visibility on the head cut; this asks the raw nonmonomial occurrence to return that tuple to the source factor.
  one-common-intertwiner-carries-the-four-pauli-pi-bridge: that is the analogous abstract affine/Atlas interface on a positive Hilbert--Schmidt carrier; this is the literal binary-Jacobson operator-norm interface and permits an arbitrarily sparse nonzero carrier.
  binary-jacobson-one-step-finite-type-envelope-is-marked-mf: that retains the entire finite packet, the balanced involution and every conjugation incidence whose two endpoints remain in the packet, and obtains a marked virtually free envelope; this asks for the alternating mixed-coefficient occurrence beyond that complete one-step type graph.
  binary-jacobson-first-mixed-kernel-is-three-syllable: that identifies the shortest alternating relation beyond the complete finite overlap as the three-balanced controlled swap; this asks for the further occurrence semantics turning mixed holonomy into one common degree-two-to-degree-four intertwiner.
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

The tail calculation is now exact.  By
`binary-jacobson-tail-phase-cannot-correct-closing-fold`, the positive
`x_13(ST)` cut is carried two-to-one onto a nonzero raw range on which the
folded tuple has PI degree at most two, while the literal native tuple on the
same range still has degree four.  The negative tail cut retains degree four.
Every scalar or unitary phase selected from the tail-center spectral algebra
leaves the erased `x_23(1)` row equal to zero, so spectral rephasing cannot
close `(JPI1)`.

The most immediate use of the remaining root is fenced as well.
`binary-jacobson-constant-opposite-polar-is-finite-s3` computes the polar of
`x_31(1)` compressed to the relevant negative constant-root cut: it is an
explicit polynomial in a finite `S_3` packet.  Thus it has no relation to the
raw `x_13(SQ)` range unless the compression visibly includes that raw cut.
The live seam is consequently a joint raw-range/opposite-root polar or
another genuinely S/T-bearing closing incidence, not a central phase or a
constant `S_3` correction.

The exact fences make the load-bearing package sharp.  Constant and
`Q`-labelled roots alone lie in the finite marked envelope of
`binary-jacobson-constant-q-root-envelope-is-finite`.  All finitary Clifford
depth and monomial `S/T` transports lie in the amenable marked-MF group of
`binary-jacobson-head-sector-has-native-clifford-tower`.  Every proper part
of the active constant three-cycle remains amenable and marked MF.  Thus the
common return must jointly consume an `S/T`-bearing occurrence and the full
nonmonomial active-cycle incidence.

Nor can the full-cycle threshold be closed by selecting a more favorable
finite `F=GL_3(2) x GL_3(2)` type graph.
`binary-jacobson-one-step-finite-type-envelope-is-marked-mf` includes every
one-step `h`-conjugation incidence which begins and ends in `F`; its marked
type graph has both a positive regular stationary profile and the direct
unitary Hall inequality.  Therefore the operation in `(JPI1)` must consume
an alternating relation in the kernel of that virtually free envelope's map
to `E`, not just central isotypes, head-sign refinements, or the nonzero block
support of `a` or `h`.

The shortest such relation is no longer unknown:
`binary-jacobson-first-mixed-kernel-is-three-syllable`
proves that three cyclic conjugates of `a` multiply to the finite
head-controlled swap, and that no nontrivial kernel word uses fewer than
three balanced syllables.  The remaining issue is therefore sharply beyond
word discovery: one must extract from this three-cell mixed holonomy (or a
further relation involving it) the common PI intertwining rows in `(JPI1)`.

There is also a shorter-looking representative at the same optimal syllable
length, and it is exactly fenced.
`binary-jacobson-shortest-affine-braid-is-finite-marked` writes the constant
Weyl word `r=w_23` using all three active cycle roots and proves

```text
(h r)^3=1,                    equivalently h r h=r h r.
```

This is a genuine non-overlap occurrence equality, but `<h,r>~=S_3`, and
adjoining its orbit of every fixed finitary Clifford packet remains finite
with the head visible.  Thus the first affine braid authenticates only
degree-preserving finite holonomy.  A successful return has to combine a
shortest relation with an additional independent raw incidence or a joint
compression not implied by either shortest relation alone.

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
