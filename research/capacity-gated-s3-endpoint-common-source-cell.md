---
rg: 2
id: capacity-gated-s3-endpoint-common-source-cell
kind: claim
title: One capacity-gated common source carries all three S3 endpoint conventions
distinct_from:
  capacity-gated-common-source-gram-word-cell: that asks for rows covering every native Fanizza context and off-capacity exit; this is the smaller three-row cell sufficient for the S3 rank-one endpoint laws.
  s3-equivariant-endpoint-conventions-use-global-bcs-words: that states the semantic conclusion; this gives a concrete ordinary-word decoder interface which implies it.
  gauge-pair-holonomy-needs-one-source-moment: that makes common Gram automatic at the analytic Hecke level; this must make its remaining mixed moment pay ordinary group-relator energy.
---

OPEN.  After simultaneous exactification of the private regular edge and one
forbidden radical fiber, decode one word-visible source projection `Q` and
three compressed rows

```text
V_b^*V_b=Q+o(1),                    b in {00,01,11}.     (SEC1)
```

For each row decode commuting binary target observables `A_(b,X),A_(b,Y)`.
Let `Z_X,Z_Y` be the two original shared-word endpoint observables before the
three chart occurrences split.  Require

```text
D_(b,X)=A_(b,X)V_b-V_bZ_X,
D_(b,Y)=A_(b,Y)V_b-V_bZ_Y.                              (SEC2)
```

On the source `Q`, the target rows must use the two diagonal and one crossed
conventions.  With `P_(b,j)=(1+A_(b,j))/2`, put

```text
F_00=Q-V_00^*P_(00,X)P_(00,Y)V_00,
F_01=  V_01^*P_(01,X)P_(01,Y)V_01,
F_11=Q-V_11^*P_(11,X)P_(11,Y)V_11.                     (SEC3)
```

The fixed ordinary-word packet must give the capacity-gated estimate

```text
sum_(b,j)||D_(b,j)||_2^2
 +sum_b tau(F_b)
 +sum_(j=X,Y)||[Q,Z_j]||_2^2
 <= K_sec E_rel+o(1),                                  (SEC4)
```

where `E_rel` is formed from the original shared Fanizza words and the named
actuator relators, and `K_sec` is independent of matrix dimension.  Equivalent
positive residual norms may replace the three traces in `(SEC4)`.

The source equality in `(SEC1)` is literal, not equality of three isotypic
dimensions.  Private sources admit the exact Bass--Serre rotation escape.
Likewise `(SEC2)` must be compressed: unconditional covariance leaves the
unpaid term `V_b[Z_j,Q]`.

This interface passes exact completeness.  On the perfect HALT witness the
selected forbidden source is zero, so all three rows may vanish.  Countable
amplification handles the remaining finite packet.  The private residual
factors stay distinct, while gauge doubling makes `Z_X,Z_Y` fixed logical
words.

The surviving Hecke candidate is explicit.  The gauge-pair free-phase cell
makes `(SEC1)` automatic, and
`orthogonal-hecke-row-packs-common-source-energy-into-one-root` packages the
six covariance defects in `(SEC2)` into one coefficient.  What remains is
the matrix-only root-to-coefficient authentication of that single mixed
moment; finite edge tables and uncompressed global conjugacy do not supply
it.  The two source commutators are not an independent load once `(SEC1)` is
exact: `labelled-pvm-branch-gram-gives-lin-corner` proves directly that

```text
[Q,Z_j]=D_(b,j)^*V_b-V_b^*D_(b,j),
||[Q,Z_j]||_2<=2||D_(b,j)||_2.                         (SEC5)
```

## Lin labelled-branch reduction

There is now a strictly weaker sufficient interface for the downstream
endpoint argument.  Suppose the shared endpoint data have first been rounded
to one labelled source PVM `(E_i)`, the three role-amplified targets to one
labelled PVM `(F_i)`, and the synchronized edge supplies contractions `T_i`
on that same reservoir.  Put

```text
G=sum_i F_iT_iE_i.                                    (SEC6)
```

By `labelled-pvm-branch-gram-gives-lin-corner`, `G` is automatically a
contraction and

```text
F_iG=GE_i,
||G||_2^2=sum_i||F_iT_iE_i||_2^2.                     (SEC7)
```

Moreover `G^*G` commutes with the whole source PVM, and every positive Lin
spectral layer carries the same exact labelled intertwining.  Thus this one
Gram state eliminates separate context gauges, covariance defects on the
retained state, and the explicit source-commutator terms.  If the target
labels retain only convention-allowed branches, their failure projections
also annihilate `G`.

Under this complete-label hypothesis, it is enough for the semantic endpoint
to prove the scalar same-reservoir mass estimate

```text
||G||_2^2>=gamma tau(Q)-K_lin E_rel-o(1)               (SEC8)
```

for some fixed `gamma>0`.  But constructing `(E_i)` from the original shared
words is part of that hypothesis when those words have not already been
jointly rounded.  Only after it is supplied is this weaker than authenticating
all of `(SEC4)`: it keeps the good matched branch mass and discards every
off-label block.

If the original two covariance rows `(SEC2)` are retained, that construction
is not a separate analytic hole.  `one-s3-row-rounds-joint-source-pvm` uses
the commuting target pair to prove

```text
||[Q,Z_j]||_2<=2||D_j||_2,
||Q[Z_X,Z_Y]Q||_2<=2(||D_X||_2+||D_Y||_2),             (SEC8a)
```

then compresses, signs, and binary-pinches the source pair to one exact
four-atom `Q`-PVM with explicit linear loss.  This observation does not make
`(SEC8)` sufficient by itself: branch mass alone controls neither commutator
in `(SEC8a)`.

The complete-label formulation is conditional: the cell does not initially
say that `Z_X` and `Z_Y` commute, so their four joint atoms cannot be assumed.
There is a hypothesis-minimal alternative.  On each role block anchor only
one binary endpoint, say `X`, and put

```text
G_X=sum_(e=+-1) ((1+eA_X)/2)T((1+eZ_X)/2).            (SEC9)
```

By `(LBG7)--(LBG11)` of
`labelled-pvm-branch-gram-gives-lin-corner`,

```text
A_XG_X=G_XZ_X,
||G_X||_2^2=tau(Q)-(1/4)||A_XT-TZ_X||_2^2,            (SEC10)
||A_YG_X-G_XZ_Y||_2<=||D_X||_2+||D_Y||_2.             (SEC11)
```

When the target pair commutes, the last residual also controls
`G_X[Z_X,Z_Y]` with constant `2`.  Thus no joint source PVM is needed before
Lin: the binary anchor is exact, while the other endpoint and the finite
`S3` role/return packet remain genuinely mixed covariance rows on this same
`G_X`.

In this formulation the exact remaining certificate is not mass alone.  On
the role amplification it is

```text
||G_X||_2^2>=gamma tau(Q)-K_mass E_rel-o(1),
E_mix(G_X)<=K_mix E_rel+o(1),                          (SEC12)
```

where `E_mix` contains the unanchored endpoint, transitive role, and return
rows.  `positive-cross-gram-state-rounds-to-common-pvm` then supplies the
fixed-density common-PVM corner.  In the complete-label variant those mixed
rows are already encoded in the labels; in the one-bit variant they are the
load-bearing non-retractive datum.

Neither the algebraic sum `(SEC6)` nor Lin's spectral theorem proves
`(SEC8)` or `(SEC12)`.  Complete PVMs and unitary branch maps admit an exact
cyclic label shift for which every compression `F_iT_iE_i` is zero.  Positive
mass by itself also supplies no role/return holonomy:
`positive-cross-gram-mass-alone-has-no-holonomy-floor` has, at every fixed
`0<gamma<1`, exact packet intertwiners with Gram mass `gamma` and an arbitrary
relative commutant gauge.  Therefore the remaining datum is one mixed,
non-retractive same-Gram relation: it must force branch mass and every
unlabelled packet covariance simultaneously.  The Lin package performs the
analytic corner extraction after that relation; it does not turn the relation
into ordinary relator energy.

## Attempts

The finite edge-table decoder was tested first.  It identifies the three
target conventions but leaves the mixed source moment unchanged, so it gives
no dimension-independent bound for `(SEC4)`.  Global conjugation has the same
defect: it transports each endpoint observable without controlling the
compressed terms `V_b[Z_j,Q]`.  The remaining attack is therefore the stated
matrix-only root-to-coefficient authentication.

The packed-root shortcut has now been tested against an exact finite model.
`s3-packed-root-has-retractive-finite-escape` gives scalar common-source data
for which all three residuals `(SEC3)` and both source commutators vanish,
while the six covariance rows have total energy `8`.  Simultaneously, the
abelianized positive-root packet over `F_5` keeps both input root lines
nontrivial and satisfies every local additivity and Steinberg triangle, but
kills the designated packed commutator root.  Exact affine `S3` covariance
and a faithful central twist do not change the escape.

Therefore ordinary root naming, even with the local multiplication table and
all finite symmetry data, cannot close `(SEC4)`.  A surviving construction
must be non-retractive: it must include a genuinely mixed relation whose
finite-matrix consequence reflects the kernel of that root coordinate back
to the concrete Hecke row on the same `Q` reservoir.  This audit does not
refute such a relation; it proves that this kernel-reflection implication,
not an omitted finite root or symmetry table, is the sole content of the
packed covariance attack.

The smallest non-retractive Julia repair has also been audited.
`one-julia-root-anchor-has-ideal-kernel-escape` ties the surviving unit root
exactly to `zjzj` in an order-250 finite semidirect product, so the whole-root
abelianization escape is genuinely unavailable and the Julia off-diagonal
block has mass `1/4`.  The unital dual-number quotient
`F_5[eps]/(eps^2)->F_5` nevertheless retains that anchor while killing the
designated coordinate `x_13(eps)`.  Thus a nontrivial constant-root anchor
does not reflect the kernel of the packed row.  Tying the designated root
directly to `zjzj` has the complementary exact absorber `j=z`, whose Julia
off-diagonal block is zero while the endpoint payload remains independent.

This leaves an even sharper interface: the mixed relation must exclude every
proper coefficient ideal containing the packed coefficient but not the unit,
or directly authenticate the Julia/Hecke off-diagonal block as the concrete
row on the same capacity reservoir.  Unit-root anchoring and a direct word
equality do neither.
