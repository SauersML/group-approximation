---
rg: 2
id: pauli-quarter-holonomy-is-balanced-derived-reset
kind: claim
title: The quarter-carrier D8 holonomy supplies a balanced derived Pauli reset seed
artifacts:
  - experiments/atlas_transported_corner_overlap.py
  - experiments/atlas-transported-corner-overlap.json
distinct_from:
  derived-lifted-gauge-reset-spin-bridge: that must attach semantic old/new gauge contexts at equal packet scale; this supplies the exact derived Pauli core but not its BCS incidence or group-word realization.
  two-sided-pauli-gauge-bridge-preserves-spin-scale: that uses an externally installed extraspecial connector; this extracts a new Pauli pair intrinsically from the two atlas quarter carriers.
---

Let `R_0,R_1` be the two carrier reflections from
`two-pauli-quarter-carriers-have-fixed-reflection-holonomy`, and put

```text
K=[R_0,R_1]=(R_0R_1)^2,
H=(1-K)/2.                                            (PDR1)
```

The exact prefix calculation gives

```text
K^2=1,
tau(K)=3/4,
H^2=H,
tau(H)=1/8.                                          (PDR2)
```

The projection `H` commutes with both reflections, and on its range

```text
H R_0 R_1 = - H R_1 R_0.                             (PDR3)
```

Thus `(R_0,R_1,K)` restricts to the unique marked two-dimensional spin type
of `D_8`.  Each old quarter cut remains exactly balanced on the new carrier:

```text
tau(H(1+R_0)/2)=tau(H(1+R_1)/2)=1/16
               =(1/2)tau(H).                         (PDR4)
```

This is the local shape required of a reset:

- the new sign `K` is literally a commutator and hence lies in the derived
  subgroup, fixing the abelianization defect of the bare semidirect reset;
- the new selector pair is transverse and balanced;
- no independent tensor qubit is added—the Pauli pair is cut out of the
  already existing overlap; and
- the carrier has fixed normalized density `1/8`.

Consequently the local representation-theoretic part of an equal-scale
derived lift is no longer hypothetical.  What remains before this closes
`derived-lifted-gauge-reset-spin-bridge` is to expose `R_0,R_1` as ordinary
derived-packet words, attach their two balanced signs to the old and fresh
gauge shares, and prove that the exact marked representation extends across
that incidence.  The exact Pauli/reset arithmetic itself is complete.
