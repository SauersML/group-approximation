---
rg: 2
id: positive-one3-global-clock-is-z3-lcs-plus-unary-sector
kind: claim
title: Global qutrit variable clocks turn positive ONE3 into Z3 equations plus one unary spectral sector
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  positive-one3-is-one-qutrit-clock-context: that uses one clock per clause and leaves equality of a fixed-space projection across occurrences; this uses one clock per global Boolean variable and leaves only exclusion of one qutrit eigenvalue.
  qutrit-fixed-space-projector-synchronizer: that asks to synchronize two already constructed fixed-space projections; no synchronization is needed here because repeated occurrences use the same global clock.
  one-hot-selector-parity-barrier: that treats binary parity selectors; this gives an exact order-three dualization and identifies its unary qutrit obstruction.
---

Let `omega=exp(2 pi i/3)`.  A positive-ONE3 system in projections `P_v`
is equivalent to the following constrained order-three system.  For every
global Boolean variable put

```text
U_v=P_v+omega(1-P_v).                                  (GQ1)
```

Then `U_v^3=1` and `spec(U_v) subseteq {1,omega}`.  For every clause
`ONE3(x,y,z)`, the clocks commute and satisfy

```text
U_x U_y U_z=omega^2.                                   (GQ2)
```

Conversely, suppose global order-three unitaries satisfy `(GQ2)`, commute
inside every clause, and obey the unary spectral restrictions

```text
Pi_(omega^2)(U_v)=0.                                   (GQ3)
```

Then `P_v=Pi_1(U_v)` is a perfect positive-ONE3 assignment.  Thus all
repeated-variable consistency is literal reuse of one global group element,
and all clause predicates are ordinary `Z_3` linear equations.  The only
nongroup relation left by this dualization is the unary two-point spectrum
condition `(GQ3)`.

The reduction is exact for finite-dimensional, tracial, Connes-embeddable,
and arbitrary von Neumann algebra representations.  It does not by itself
groupify positive ONE3:
`two-point-qutrit-spectrum-is-not-fixed-sector-group-gadgetizable` shows
that `(GQ3)` cannot be imposed by a complement-free ordinary-group gadget in
the fixed `J=omega` sector.

DERIVATION
positive-one3-global-clock-dualization-proof
