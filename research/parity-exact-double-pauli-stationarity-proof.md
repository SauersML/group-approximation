---
rg: 2
id: parity-exact-double-pauli-stationarity-proof
kind: route
title: Duplicate each Pauli reflection into its own exact parity face
target: parity-exact-double-pauli-is-stationary-for-intrinsic-green-step
requires:
  - intrinsic-finite-green-commutator-step-has-the-correct-tangent
  - parity-exact-shared-contractions-have-intrinsic-cp-gap
  - regularized-anchor-square-function-has-dimension-free-cut
---

The check matrix with rows `(1,1,0,0)` and `(0,0,1,1)` has kernel `(PED1)`;
its nonzero weights are `2,2,4`.  Thus the relative distance is `1/2`, and
the two displayed rows cover all coordinates.

Substitution of `(PED2)` proves exact local commutation and parity.  For
equal Pauli letters `(Q_iQ_j)^2=I`; for opposite letters anticommutation
gives `(Q_iQ_j)^2=-I`.  This proves `(PED4)`.  Since all `c_i` are scalar,
the ucp map `A_Q` and every power of it fix them.  The Green outputs are
selfadjoint, so the skew conjugators in `(IFG3)` vanish.  The intrinsic map
is therefore stationary for every finite Green depth.

There are eight ordered cross-pair positions.  Each commutator has squared
normalized Hilbert--Schmidt norm `4`, proving `(PED5)`.  Finally the anchor
odd part is zero on the anchor's duplicate pair and is the opposite Pauli
reflection on the other pair.  Averaging its four squares gives `(PED6)`.
All formulas are preserved on a central direct summand, proving the dilution
statement and the exact location of the aggregate-cut escape.
