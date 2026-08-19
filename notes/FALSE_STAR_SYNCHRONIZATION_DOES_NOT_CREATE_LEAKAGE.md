# Star synchronization preserves leakage instead of orienting it

Date: 2026-08-14

## Outcome

The two-sheet extension in `TRUE_RAW_STAR_SYNCHRONIZED_SECTOR.md` correctly
turns Leavitt star into a spatial adjoint operation.  It does not create the
one-way leakage required by the atlas obstruction.  This remains true after
combining the extension with arbitrary coefficient-space holonomy.

Let the two sheets carry matrices `W0,W1` and cuts `P0,P1`.  Put

```text
W = diag(W0,W1),        P = diag(P0,P1).
```

Then block multiplication gives the exact identities

```text
(1-P) W P
  = diag((1-P0)W0P0, (1-P1)W1P1),

P W (1-P)
  = diag(P0W0(1-P0), P1W1(1-P1)).                    (SSL1)
```

Normalized Hilbert--Schmidt mass on the doubled space is the average of the
two sheet masses.  Consequently

```text
||(1-P)WP||_2^2
 = (||(1-P0)W0P0||_2^2+||(1-P1)W1P1||_2^2)/2,

||PW(1-P)||_2^2
 = (||P0W0(1-P0)||_2^2+||P1W1(1-P1)||_2^2)/2.        (SSL2)
```

If `W0,W1` are unitary and `P0,P1` are projections, finite one-cut balance
holds separately on each sheet.  Averaging therefore gives

```text
||(1-P)WP||_2=||PW(1-P)||_2.                         (SSL3)
```

Thus doubling preserves the obstruction's symmetry; it cannot orient it.

The formulas `(SSL1)--(SSL2)` are formalized source-first in
`GroupApproximation/Sofic/InvolutiveTwoSheet.lean` as

```text
twoSheetDiagonal_forwardLeakage
twoSheetDiagonal_reverseLeakage
hsNormSq_twoSheetDiagonal_forwardLeakage
hsNormSq_twoSheetDiagonal_reverseLeakage.
```

No local build was run.

## The sheet swap does not help on the raw cut

The star extension uses

```text
J = [0 1]
    [1 0].
```

For the raw involution `r`, the star automorphism fixes `r`, hence it fixes
the negative cut `e=(1-r)/2`.  On the doubled model this cut is
`diag(e,e)`, and the exact swap identity gives

```text
J diag(e,e) J=diag(e,e).
```

Therefore `J` commutes with the carrier and has zero leakage in both
directions.  Multiplying a diagonal transport by `J` merely exchanges the
two equal carrier sheets; it does not alter `(SSL2)`.

More generally, an arbitrary multiplicity holonomy `C` becomes
`diag(C,psi(C))`.  Its leakage is still the average of the original
holonomy and its involutive mate.  The extension spatializes the adjoint but
does not restrict `C`.

## Research consequence

The star synchronizer remains useful, but only for its advertised role:
identifying opposite-root Fourier blocks with genuine Hilbert-space
adjoints.  It cannot supply support containment or a directed index by
itself, even when combined with the two raw compressor covariance equations.

The smallest live atlas theorem is unchanged and now more sharply delimited:

> use a cross-root multiplication relation to resolve the two extension
> fibers inside one finite multiplicity algebra, then prove either common
> support containment or asymmetric leakage there.

Any argument whose only new ingredients are diagonal two-sheet doubling,
the swap `J`, and unitary one-cut balance is closed by `(SSL1)--(SSL3)`.
