---
rg: 2
id: partial-isometry-translate-cancel-charges-first-exit
kind: claim
title: Partial-isometry triangle cancellation charges exactly the missing source or range
distinct_from:
  native-parahoric-triangle-kills-all-corrector-gauges: that performs two unitary translate-and-cancel steps on a common carrier; this proves the supported version in which failure of cancellation is measured by explicit source/range leakage.
  six-edge-holonomy-energy-ledger-is-scale-free: that telescopes six already-supported gallery transitions and charges nontrivial returned holonomy; this supplies the local supported cancellation inequality used to construct or shrink those transitions.
  kazhdan-polar-rounding-produces-supported-gallery-edges: that constructs an exact partial intertwiner once endpoint group actions have been corrected; this is a purely operator-theoretic estimate for using such an intertwiner without any additional exactification.
---

Let `(M,tau)` be a finite tracial von Neumann algebra with normalized
Hilbert--Schmidt norm.  Let `R` be a projection.

## Supported cancellation

If `A` is a partial isometry with initial projection

```text
P=A^*A <= R,                                             (PIT1)
```

then for every contraction difference `X` with `||X||_infinity<=2`,

```text
||R X||_2^2
 =||P X||_2^2+||(R-P)X||_2^2
 <=||A X||_2^2+4 tau(R-P).                              (PIT2)
```

Likewise, if `B` is a partial isometry with final projection

```text
Q=BB^* <= R,                                             (PIT3)
```

then

```text
||X R||_2^2<=||X B||_2^2+4 tau(R-Q).                    (PIT4)
```

The identities use `||AX||_2=||PX||_2` and
`||XB||_2=||XQ||_2`.  Thus a partial isometry cancels isometrically on its
actual source or range; the only uncontrolled part is its literal missing
carrier mass.

## One translated triangle

Let `Z,Z',A,A',B,B'` be contractions, with `A` as in `(PIT1)`, and put

```text
e_0=||Z-AB||_2,
e_1=||Z'-A'B'||_2,
f=||Z-Z'||_2,
g=||A-A'||_2.                                           (PIT5)
```

Then

```text
||R(B-B')||_2^2
 <=(e_0+e_1+f+g)^2+4 tau(R-P).                          (PIT6)
```

Indeed

```text
A(B-B')=(AB-Z)+(Z-Z')+(Z'-A'B')+(A'-A)B',              (PIT7)
```

and `(PIT2)` applies.  Dually, if `B` has final projection `Q<=R`, then

```text
|| (A-A')R ||_2^2
 <=(e_0+e_1+f+||B-B'||_2)^2+4 tau(R-Q).                 (PIT8)
```

This is precisely the approximate version of left or right cancellation in
the native ordered corrector triangle.

## First-exit interpretation

Apply `(PIT6)` to the triangle and its `x_32(1)`-translate from
`native-parahoric-triangle-kills-all-corrector-gauges`.  On the initial
projection of the first supported factor, the second factor becomes
invariant under the translated positive root with dimension-free error.
Every direction on which this conclusion is unavailable lies in `R-P` and
has trace charged explicitly by `(PIT6)`.  Apply `(PIT8)` to the
`x_21(1)`-translate for the other positive root.  Subsequent telescoping of
the two signed Weyl words has the same form: at every letter, mass either
continues through the next partial isometry or enters its missing
source/range projection.

Consequently, on any finite supported gallery packet, the exact estimate
`(NPC15)` has the schematic supported form

```text
||R(Z-I)||_2^2
 <= C edgeEnergy + C sum(firstExitMass),                (PIT9)
```

where `C` depends only on the fixed two triangles and two three-letter Weyl
words.  It is independent of ambient matrix dimension, conductor depth, and
root-clock period.  No rank deletion is used: the discarded quantity in
`(PIT9)` is already the trace of an actual projection.

Thus **after** the relevant partial transitions have been supplied, the
common-carrier-or-first-exit dichotomy required by the arithmetic hexagon
decoder is automatic.  The remaining extraction gate is to produce those
supported factors from the raw canonical microstate and prove that their
missing sources/ranges enter the conductor ledger; nonunitarity of the
factors creates no further analytic obstruction.
