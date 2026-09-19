---
rg: 2
id: branch-flip-pauli-extraction-cancels-schur-surplus
kind: claim
title: Turning the Schur branch flip into a Pauli cell cancels the multiplicity surplus
invalidates:
  - nekrashevych-violation-recurrence-via-partial-center-return
distinct_from:
  schur-child-center-sign-flip-is-group-automorphism: that correctly pairs the two child types; this computes what happens when the pairing implementer is promoted into the returned matrix factor.
  stationary-type-mass-reused-on-infinite-amalgams: that treats reuse of a scalar flow across a tree; this is the local Morita cancellation which creates that stationary scalar.
---

Let `C_f=B_f^Q`, let `q_*=q_(N+1)`, and let `eta` implement the corrected
branch flip `q_*->Jq_*`.  The subgroup

```text
L=<J,q_*,eta>
```

is a genuine Pauli group: `q_*^2=eta^2=J^2=1` and
`[eta,q_*]=J`.  Moreover

```text
L intersect <J,z_1,...,z_k> = <J>.                              (BFC1)
```

Thus `L` passes the selector-center intersection test.  It fails the
multiplicity test.  On a violating sector, a full Schur simple restricts to
the `Q` child as

```text
S tensor (C_+ directSum C_-).
```

Adjoining `eta` exchanges the two lines, so `q_*` and `eta` generate `M_2`
on their sum.  The two child copies are thereby recombined into one spin
module.  Equivalently,

```text
C[C_2] semidirect C_2 = M_2
```

on the negative central sector.  The factor-two restriction multiplicity is
consumed exactly when the proposed new Pauli prefix cell is formed.

On the translation-symmetrized full reset this is the scalar ray computed in
`(SRC6)--(SRC7)`: after every selector and branch flip is adjoined, only one
stationary multiplicity parameter `n` remains.  Therefore the proposed
partial-center Thompson return cannot satisfy `(SVG2)--(SVG3)` with a strict
surplus.  A valid return may use the flip to **balance** a child chart, but it
must transport the restriction to that child before adjoining the flip to the
returned spin algebra.  The Thompson Pauli tape does not itself perform that
Morita return.

