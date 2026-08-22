---
rg: 2
id: cartantype-mackey-cocycle-is-pauli-and-locally-absorbed
kind: claim
title: The first diagonal dyadic Mackey cocycle is Pauli rank two and has a stationary local absorber
artifacts:
  - experiments/sl3_mod4_cartantype_mackey.py
  - experiments/sl3_mod4_cartantype_mackey.json
distinct_from:
  nonzero-diagonal-clifford-type-closes-all-six-local-cycles: that closes the coadjoint-orbit labels and leaves the stabilizer extension open; this computes the first stabilizer cocycle and cancels it on multiplicity.
  p3-full-parahoric-interlock-enforces-inverse-mackey-cocycle: that treats the odd-prime oscillator packet; this is the dyadic Cartan type in the depth-two congruence kernel.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that is the abstract cancellation theorem; this supplies the exact arithmetic cocycle to which it applies.
---

For

```text
X=diag(1,-1,0) in sl_3(Z/4Z),
H=Stab_(SL_3(Z/4Z))(X),                                (CMC1)
```

one has

```text
H ~= (Z/2)^4.                                           (CMC2)
```

Lift `H` through elementary words to `SL_3(Z/16Z)` and evaluate the
resulting section cocycle against the character `chi_X` of the depth-two
kernel.  The scalar cocycle takes values in `{+1,-1}`, is not a coboundary,
and its alternating commutator bicharacter on `H` has rank `2` over `F_2`.
In one computed basis its matrix is

```text
[0 1 1 0]
[1 0 0 0]
[1 0 0 0]
[0 0 0 0].                                              (CMC3)
```

Thus the obstruction is exactly one Pauli pair: every irreducible projective
representation for this cocycle has dimension `2` (with four choices from
the two-dimensional radical).  The character does not extend linearly to
its inertia group, but tensoring its projective intertwiner with the
conjugate two-dimensional projective representation cancels the cocycle and
gives an honest local transport.

More generally, adding all six directional arrows produces a finite
projective sector groupoid on any fixed congruence window.
`finite-projective-sector-groupoids-have-conjugate-absorbers` supplies a
stationary conjugate multiplicity for the whole groupoid at once.  Therefore
neither the nontrivial rank-two cocycle `(CMC3)` nor any other FIXED-DEPTH
Mackey cocycle can furnish the uniform dyadic transfer gap.  The remaining
possibilities are an obstruction whose projective rank grows with the depth
window, an unbounded-history incompatibility, or an additive multi-path
interference not described by a projective groupoid.

There is no rescue from making the finite window or its cocycle rank grow.
`regular-dyadic-windows-have-unlimited-conjugate-mackey-capacity` uses
`lambda_Q tensor conjugate(lambda_Q) ~= |Q| lambda_Q` to place each
conjugate absorber inside an amplified regular congruence block, preserving
both canonical character and conductor.  The remaining issue is not
multiplicity capacity but whether the required cross-depth arrows occupy
one literal arithmetic carrier.
