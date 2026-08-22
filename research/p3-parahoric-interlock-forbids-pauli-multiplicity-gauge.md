---
rg: 2
id: p3-parahoric-interlock-forbids-pauli-multiplicity-gauge
kind: claim
title: The full p-three parahoric interlock forbids Pauli cancellation of odd-depth Maslov holonomy
distinct_from:
  p3-minus-flux-is-cancelled-by-pauli-multiplicity: that is the exact finite oscillator-plus-multiplicity escape; this is the additional full-parahoric assertion needed to exclude it.
  lambda-exact-face-closes-at-p-three: that is the assembled commutant collapse statement; this is only its narrow multiplicity-gauge authentication seam.
  arithmetic-hexagon-decoding-or-conductor-leakage: that asks to decode an A2 carrier from arbitrary root microstates; this starts after an oscillator band and its parahoric transports have been decoded and controls only their multiplicity factors.
---

OPEN.  On every deep odd-conductor oscillator band in a finite
`SL_3(Z/3^a)` packet, the two coweight routes around the native `A_2`
parahoric hexagon have scalar oscillator quotient `-1`.  The remaining
multiplicity operators are constrained by the Weyl and opposite-root
interlocks so that their quotient is asymptotically `+1`, not the Pauli
class `-1`, with a dimension-independent normalized-HS modulus.

Equivalently, a positive carrier cannot realize the exact escape

```text
A'=A tensor X,          B'=B tensor Z
```

from `p3-minus-flux-is-cancelled-by-pauli-multiplicity` while satisfying
the full finite parahoric relation set.  Combined with
`one-shift-folner-mass-is-depth-parity-balanced`, this assertion removes the
invalid flatness step: one-shift covariance forces half the deep mass onto
odd depth, while the authenticated `-1` loop forces the good odd carrier to
vanish by `(PBF3)`.

This is the narrow dictionary seam.  Bare Stone--von Neumann uniqueness,
the computed Gauss sign, and Heisenberg covariance do not prove it; the
exact Pauli countermodel satisfies all three.  A proof must use at least one
specific Weyl/opposite-root relation acting nontrivially on the
multiplicity coordinate.

## Attempts

- **Stone--von Neumann plus the Gauss sign.**  Insufficient by the exact
  `X,Z` tensor model: it preserves every Heisenberg covariance equation.
- **Apply Schur's lemma on the oscillator constituent.**  This controls the
  irreducible oscillator factor only.  An isotypic block is
  `pi tensor C^m`, and its intertwiner algebra is `M_m`; the Pauli escape
  lives entirely there.
- **Next finite calculation.**  Choose one explicit opposite-root or Weyl
  generator from the full level-`3^a` parahoric that preserves the band and
  compute its action on `M_m`.  A usable result must show that simultaneous
  covariance with this generator forces both multiplicity transports into
  a common commutative/scalar algebra with a dimension-independent gap.
  No such multiplicity action is identified in the current dictionary, so
  the attack is deferred at exactly this representation-theoretic datum.
