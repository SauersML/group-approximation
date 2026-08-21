---
rg: 2
id: derived-reset-packets-do-not-saturate-both-children
kind: claim
title: Balanced derived-reset packets do not saturate both child sources
distinct_from:
  authenticated-pauli-branch-needs-source-saturation: that proves the analytic recurrence once two full-source moments are supplied; this audits whether the existing Pauli, derived-reset, and Schur packets actually supply those moments.
  pauli-two-child-transfer-packet: that constructs two exact equal-source arrows from a smaller source into a doubled target; this proves why the existing balanced reset cannot return that doubled target to the same source scale.
  branch-flip-pauli-extraction-cancels-schur-surplus: that shows the Pauli flip consumes the Schur factor two; this expresses the same cancellation as a sharp source-Gram rank obstruction for the PAZ return.
---

Let

```text
P_Y=(I-Y)/2                                             (DRS1)
```

be the authenticated PAZ return carrier from
`graph-commutator-authenticates-paz-return`.  To finish `(PAG19)`, one would
like to obtain contractions `S_0,S_1` and orthogonal child tags
`B_0,B_1<=P_Y` with

```text
S_i^*S_i approx P_Y,
(I-B_i)S_i approx0.                                    (DRS2)
```

The existing equal-scale derived reset and Schur rank-doubling packets do
not imply `(DRS2)` after fixed finite-packet exactification.  Their
restriction matrix is stationary: it determines a total multiplicity-two
reservoir, not two copies of that entire reservoir.

## The balanced reset restriction matrix

The affine derived-reset bridge has, on both its old and fresh selected
sides, the exact edge restriction

```text
Res_H(pi_old)=2 rho_15,
Res_H(pi_new)=2 rho_15.                                (DRS3)
```

After taking `n` copies of a selected outer type, the relevant edge carrier
is therefore

```text
rho_15 tensor C^(2n).                                  (DRS4)
```

Finite-group exactification and polar alignment identify the two spaces
`C^(2n)` by one unitary.  They do not select a preferred decomposition

```text
C^(2n)=C^n direct_sum C^n.                             (DRS5)
```

Indeed the edge packet acts trivially on the multiplicity factor, whose
commutant is the full algebra `M_(2n)(C)`.  Conjugating by an arbitrary
`U(2n)` changes `(DRS5)` while preserving every exact finite packet and edge
restriction relation.

Thus `(DRS3)` has two possible readings, neither of which gives `(DRS2)`:

1. take the whole `2n`-dimensional multiplicity space as the source; then
   each child has only `n` dimensions and cannot have full source Gram;
2. select one `n`-dimensional half as the source; then both children may
   have the correct size, but the source half is a free multiplicity
   orientation not authenticated by the packet.

## Sharp half-rank source-defect floor

The first obstruction has a dimension-independent exact bound.

### Theorem 1

Let `P` be a projection of rank `2n`, let `B` be a projection of rank at
most `n`, and let `S` be a contraction with range in `B`.  With normalized
trace on `PH`,

```text
||S^*S-P||_2^2>=1/2.                                   (DRS6)
```

For an ambient normalized trace, the equivalent bound is

```text
||S^*S-P||_2^2>=tau(P)/2.                              (DRS7)
```

### Proof

The positive contraction `S^*S` has rank at most `n`.  Hence at least `n`
of its eigenvalues on the `2n`-dimensional range of `P` are zero.  On each
such direction `(S^*S-P)^2` has eigenvalue one.  Dividing by `2n` proves
`(DRS6)`; multiplying by the ambient carrier mass proves `(DRS7)`.  ∎

Consequently no sequence of exactified balanced reset packets can make both
source defects in `(DRS2)` vanish while using the full carrier `(DRS4)`.
The obstruction is not an estimate lost in polar rounding; it is a rank
floor of one half.

## The Pauli branch doubles the target, not the returned source

The exact packet in `pauli-two-child-transfer-packet` has

```text
T_i^*T_i=E,
T_iT_i^*=R_i,
R_0R_1=0,
R_0+R_1=F,                                             (DRS8)
```

with

```text
tau(E)=tau(R_0)=tau(R_1)=1/8,
tau(F)=1/4.                                            (DRS9)
```

This supplies two genuinely saturated children for source `E`.  But their
combined target is the doubled carrier `F`, not a subprojection of `E`.
The one-step recurrence is exactly stationary:

```text
tau(E)=[tau(R_0)+tau(R_1)]/2=1/8.                      (DRS10)
```

Closing the PAZ recurrence requires returning `F` to the same carrier `E`.
No finite-packet unitary or equal-scale reset can do that: unitary transport
preserves trace, while `tau(F)=2tau(E)`.  Relation `(DRS3)` aligns equal
`2rho_15` restrictions and therefore preserves, rather than removes, this
factor-two reservoir.

Imposing an exact proper-corner return `F` to `E` in the group algebra would
make the faithful regular trace say `2tau(E)=tau(E)`, killing `E` and the
mark algebraically.  The return must therefore be matrix-coordinate only;
it is not a consequence of fixed packet exactification.

## Schur surplus is consumed by the derived Pauli flip

On a violating selector sector, the Schur simple restricts to the residual
child as

```text
S tensor (C_+ direct_sum C_-).                         (DRS11)
```

The factor two in `(DRS11)` is the desired multiplicity surplus.  The
corrected branch-flip implementer exchanges `C_+` and `C_-`.  Once promoted
into the returned Pauli algebra, those two lines become one irreducible
two-dimensional spin module.  In restriction-matrix language,

```text
(1,1) child multiplicity
  -> one M_2 spin block.                               (DRS12)
```

Thus the same move which makes the reset a legal derived Pauli phase consumes
the factor two that would have powered the two full-source moments.  The
balanced four-point gauge packet confirms this: exactly one complementary
Pauli pair is active in either selector sign, so the spin rank is constant
across the reset rather than supercritical.

The Schur surplus may be transported **before** adjoining the flip, but then
one again needs a mixed multiplicity orientation selecting the two child
copies in `(DRS11)`.  Fixed packet exactification sees only their sum.

## Stationary restriction-matrix countermodel

The obstruction is realized exactly, not just infinitesimally.

Take the finite graph of the old reset packet, the common edge packet, and
the fresh reset packet.  Assign `n` copies of each selected outer type.  By
`(DRS3)`, both edge restrictions have multiplicity vector `2n rho_15`, so an
arbitrary unitary on `C^(2n)` glues them exactly.  Add the finite Pauli branch
packet `(DRS8)` and choose the stationary type vector

```text
E : R_0 : R_1 = n : n : n.                            (DRS13)
```

All finite packet tables, reset relations, edge restrictions, derived-sign
relations, and child orthogonality relations hold exactly.  The multiplicity
flow is positive and stationary.  The graph-of-finite-groups realization
theorem supplies an exact finite-dimensional representation for every
integral `n` after a common amplification.

Tensor/central-product this model with the finite authenticated PAZ model

```text
G=I,
W=-I,
Y=[A,B]=-I.                                            (DRS14)
```

The authenticated return and all existing packet relations remain exact,
while `(DRS6)` prevents the two maps from the total returned reservoir from
having full source Gram.  Alternatively, selecting a rank-`n` half makes
the free `U(2n)` orientation rotate it away from the analytic `P_Y` source.

This is the exact stationary/rectangular countermodel requested by the
audit.  It survives every currently available fixed-packet relation and
fails only the two source moments `(DRS2)`.

## What additional relation would be sufficient

No operator-valued source equality is necessary.  By
`authenticated-pauli-branch-needs-source-saturation`, it is enough to force
the two scalar inequalities

```text
tau(S_i^*S_i)>=tau(P_Y)-e_i,             i=0,1,        (DRS15)
```

together with range leakage into orthogonal child tags.  The stationary
model shows that `(DRS15)` cannot follow from:

```text
equal restriction multiplicities,
derived reset covariance,
Schur factor-two restriction,
Pauli child orthogonality,
canonical finite-packet trace.                         (DRS16)
```

A successful relation must break the free `U(2n)` multiplicity orientation
and couple **both** selected child halves to the same analytic `P_Y` source.
It must do so only in finite matrix coordinates, because a universal
proper-corner inclusion collapses the regular mark.

This is a strict narrowing: the missing rigidity is not another reset sign,
rank balance, or Clifford table.  It is one matrix-only orientation/return
moment on the doubled edge multiplicity reservoir.

## Attempts

- **Use the equal-scale derived reset as the return.**  Its restriction is
  `2rho_15` on both sides, so it identifies total `2n` reservoirs and leaves
  the decomposition `(DRS5)` free.
- **Use each of the two restriction copies as a child of the whole source.**
  The half-rank floor `(DRS6)` gives source defect at least `1/2`.
- **Choose one restriction copy as the source.**  Packet relations are
  invariant under `U(2n)` on multiplicity, so no canonical or analytic source
  alignment follows.
- **Use the Pauli transfer cell and then reset `F` to `E`.**  Their traces
  differ by two.  A universal return kills the regular carrier; an
  equal-scale reset preserves the doubled size.
- **Use the Schur rank surplus after adjoining the branch flip.**  The flip
  combines the two child lines into one Pauli spin block and cancels the
  surplus exactly.

## Verdict

The existing packets do not instantiate the two PAZ child source moments.
Their sharp obstruction is the balanced restriction matrix

```text
2rho_15 <-> 2rho_15,                                   (DRS17)
```

whose multiplicity commutant is `M_(2n)` and whose stationary positive flow
contains the regular finite model.  Either one uses the full `2n` source and
pays the rank-`1/2` defect `(DRS6)`, or one selects an `n`-dimensional half
and reintroduces the unauthenticated multiplicity orientation.  The sole
remaining relation is therefore a finite-dimensional-only same-source
orientation/return moment; no current equal-scale reset or rank-doubling
packet implies it.
