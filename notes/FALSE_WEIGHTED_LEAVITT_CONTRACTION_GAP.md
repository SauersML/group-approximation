# Positive spectral mass does not give a compressed Leavitt gap

Date: 2026-08-14

## Outcome

The positive-density spectral sector from
`TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md` cannot by itself be fed into the
multiplicative Leavitt contraction gap.  Common-sector invariance is not a
technical convenience: without it there is an exact two-dimensional
countermodel.

Let

```text
P  = [1 0]       S0 = T0 = P,
     [0 0]

S1 = [0 0],      T1 = [0 1].
     [1 0]            [0 0]
```

All four arrows are contractions.  The carrier `P` is a rank-one projection,
so it has normalized trace `1/2`.  Nevertheless,

```text
T0 S0 P = P,
T1 S1 P = P,
T0 S1 P = 0.                                      (WLC1)
```

Thus the two diagonal right-inverse relations and the crossed-zero relation
hold exactly after testing on a positive-density proper carrier.  The
mechanism is elementary: `S1` moves the carrier line to its orthogonal line,
and `T1` moves it back.  The crossed product `P S1 P` vanishes precisely
because the intermediate vector has left the carrier.

The identities `(WLC1)` are formalized source-first in
`GroupApproximation/Sofic/LeavittTraceFloor.lean` as
`properCarrier_exact_weighted_leavitt_relations`.  The carrier's diagonal
entries, certifying that it is nonzero and proper, are recorded as
`weightedLeavittCarrier_diagonal`.  Per the project instruction, no local
build was run.

## What this rules out

There can be no dimension-free theorem of the form

```text
positive trace(P)
+ a singular-value floor on P
+ small compressed product defects on P
=> a positive Leavitt defect floor
```

unless an additional hypothesis prevents the arrows from escaping `P`.
The example already has trace `1/2`, exact products, and unit singular value
on the relevant transition.  Improving the `1/120` density or the `1/4`
singular-value bound therefore cannot repair the missing implication.

The same example blocks naive iteration along a finite branch tree.  Once an
intermediate image leaves the spectral carrier, later estimates restricted to
the original carrier do not control it.  Merely accumulating more compressed
word relations does not restore the full-space trace identity.

## What remains live

The full-space theorem in `LeavittTraceFloor.lean` is unaffected.  Its sharp
contraction gap applies once all arrows act on one common finite-dimensional
space.  For the spectral route, one must prove at least one of:

1. the selected positive-density sector is approximately invariant under all
   four recovered arrows;
2. the orbit of the selected sector contains a common positive-density
   reducing subprojection; or
3. leakage from the sector has a fixed positive lower bound that directly
   contradicts a separate balance identity.

Accordingly, the hyperlinear endpoint is now narrower.  The trace-flat comb
calculation supplies density and conditioning, while the only missing
analytic bridge is a **common-sector invariance or leakage theorem tied to
the actual group words**.  Weighted trace estimates alone cannot replace it.
