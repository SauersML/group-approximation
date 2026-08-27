---
rg: 2
id: clifford-groupified-control-is-forced-balanced
kind: claim
title: Pauli completion forces every groupified control corner to have half the marked mass
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that proves the positive covariance theorem after Pauli completion; this records the exact trace constraint introduced by the required conjugate partner.
  relative-pauli-child-split-gives-one-exit-copy: that constructs a balanced child sign from a Schur rank jump; this proves balance is necessary for using that sign as a Clifford control.
---

Let `J,z,x` be involutions satisfying

```text
J central,       [x,z]=J,
```

and let `Q=(I-J)/2`. In every finite tracial representation,

```text
tau(Q (I-z)/2)=tau(Q (I+z)/2)=tau(Q)/2.               (CGB1)
```

Indeed, on `Q` the relation is `x z x=-z`, so conjugation by `x` exchanges
the two `z` spectral projections. The same equality holds in every finite
von Neumann tracial representation.

Consequently Pauli/Clifford completion cannot groupify a controlled operation
on a corner of arbitrary marked trace. It is compatible exactly when the
control already comes with a balanced conjugate pair, as happens for the
relative-Pauli halves of a violating Schur rank gate. If a reset cell uses a
raw BCS selector or a child branch with variable weight as its control,
Pauli completion changes the intended incidence rather than merely
groupifying it.

Quantitatively, if the central and commutator relators have normalized-HS
error at most `delta`, fixed-length telescoping gives

```text
|tau(Q(I-z)/2)-tau(Q)/2| <= C delta,                  (CGB2)
```

after replacing the almost involutions by their spectral involutions. For a
fixed Pauli packet this also follows from flexible finite-group
exactification, with `C` independent of matrix dimension.
