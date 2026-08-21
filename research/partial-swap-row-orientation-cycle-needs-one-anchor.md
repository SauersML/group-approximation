---
rg: 2
id: partial-swap-row-orientation-cycle-needs-one-anchor
kind: claim
title: Partial-swap rows ignore global signs, while a relative-orientation cycle still needs one anchor
distinct_from:
  controlled-reflection-cell-has-free-orientation: that computes the hidden multiplicity involution in a fresh-control acceptance compressor and shows that it changes the acceptance corner; this separates the harmless whole-row sign in the partial-swap compiler from the harmful relative block sign.
  derived-reset-does-not-fix-controller-orientation: that proves a balanced derived lift preserves both controller extension characters; this gives the exact parity reason that a finite cycle of row comparisons also preserves the simultaneous relative twist.
  dihedral-spin-packet-supplies-common-partial-swap: that supplies the common off-diagonal Gram source and reduces the remaining problem to hybrid row involutions; this audits precisely which orientation ambiguity of those row involutions matters.
---

Fix a grading involution `Z=diag(I,-I)` and a self-adjoint involution

```text
J=[[a,S],[S^*,d]]                                     (ORC1)
```

whose off-diagonal block is the common Gram partial isometry.  A hybrid row
involution has the intended form

```text
D=diag(A,B),                                          (ORC2)
```

where `A,B` are self-adjoint unitaries.  There are two different orientation
ambiguities, and they must not be conflated.

## Whole-row signs are exactly harmless

For every scalar `epsilon in {+1,-1}`,

```text
[epsilon D,J]_add=epsilon[D,J]_add,
(epsilon D)J(epsilon D)J=DJDJ.                       (ORC3)
```

The off-diagonal Gram row is changed only by the same scalar:

```text
epsilon(AS-SB).                                       (ORC4)
```

Thus even an independent character twist `D_r -> -D_r` for every test row
leaves every partial-swap commutator relator and every row energy **exactly
unchanged**.  The common-swap game compiler does not need to select or
synchronize this global sign.  In particular, the free scalar orientation
which obstructs the fresh-control cyclic acceptance compressor is not by
itself an obstruction here.

For the predicate row `D=diag(I-2F,I)`, the opposite whole-row orientation
`diag(-(I-2F),-I)` still pays exactly `4||FS||_2^2`.

## Relative block signs are load-bearing

Multiplication by the grading gives

```text
ZD=diag(A,-B).                                        (ORC5)
```

Its off-diagonal row is `AS+SB`, not `AS-SB`.  The two orientations obey
the exact parallelogram identity

```text
||AS-SB||_2^2+||AS+SB||_2^2=4||S||_2^2.              (ORC6)
```

Hence the correct and relatively flipped rows cannot both have small defect
on a positive-mass common source.  A tautological anchor with `A=B=I`
distinguishes them maximally: the intended row is zero and the flipped row
has squared norm `4||S||_2^2`.

## A finite cycle does not choose the relative orientation

Abstract the remaining extension ambiguity by bits `t_v in {+1,-1}`, where
`t_v=-1` means that the `v`-th hybrid row has been multiplied by `Z`.
Every pairwise comparison which only fixes relative orientation has the
form

```text
t_v t_w=sigma_(vw).                                   (ORC7)
```

For an intended consistently oriented cycle, the product of the edge signs
is `+1`.  Whenever `(t_v)_v` solves `(ORC7)`, so does `(-t_v)_v`.  On a
connected cycle these are exactly the two scalar solutions.  Adding more
edges or replacing the cycle by an expander still leaves the simultaneous
twist.

The operator-valued stationary model is equally exact.  Let `u` be any
multiplicity involution commuting with all visible row data and put the
same hidden `u` on every vertex.  All ratio, commutator, and even-incidence
cycle checks cancel `u`; the choices `u=I` and `u=-I`, and arbitrary direct
sums of the two, survive with zero defect.  This is the controller twist
from `controlled-reflection-cell-has-free-orientation` distributed
stationarily around the cycle.

Therefore a finite cyclic self-verifier can synchronize **relative
differences**, but it cannot orient the resulting connected component.
One anchored vertex is necessary and sufficient at the bit level.  A tree
from that anchor already suffices; cyclic redundancy or expansion only
improves robustness after the anchor has been wordized.

## Consequence for the hybrid-row compiler

The remaining orientation target is narrower than selecting a unique finite
representation type:

1. ignore every whole-row sign by `(ORC3)`;
2. couple all relative block-orientation bits to one common bit; and
3. pay that one bit with a tautological row or one fixed Hecke-corner anchor.

Step 3 is still a genuine group-word problem.  The anchor must compare the
two `Z` blocks on the common dihedral spin source; a cycle of unanchored
extension-character comparisons cannot manufacture it.  Once such an
anchor is available, `(ORC6)` gives a dimension-independent source-mass
floor for the wrong orientation, and no per-predicate orientation selection
is needed.

## Attempts

- **Kill all scalar signs.**  Unnecessary: `(ORC3)` shows that they cancel
  from the exact multiplicative relator.
- **Use an odd or expanding cycle of pairwise row comparisons.**  The
  simultaneous relative twist preserves every edge equation and has an
  exact multiplicity-space realization.
- **Anchor a reference row with `A=B=I`.**  Analytically complete by
  `(ORC6)`; the open issue is naming its relative `Z`-block orientation by
  ordinary words on the same source.
