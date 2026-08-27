---
rg: 2
id: two-quarter-carriers-resist-short-packet-transport
kind: claim
title: No packet word of length at most two transports the two trace-quarter carriers
artifacts:
  - experiments/atlas_quarter_carrier_short_conjugacy.py
  - experiments/atlas-quarter-carrier-short-conjugacy.json
distinct_from:
  transported-coefficient-corners-share-flat-quarter-carrier: that identifies and fingerprints the capacity-generated common corner; this rules out the shortest raw/comb packet symmetries as a bridge to the branch-transfer carrier.
  pauli-carrier-membership-decoder: that asks for a matrix-coordinate mixed-relation decoder; this is only a bounded exact no-shortcut audit.
---

Let `F_cap` be the common trace-quarter projection from the two transported
coefficient corners, and let `F_branch` be the comb-transported trace-quarter
carrier from the Pauli branch-transfer packet.  In the exact binary
Leavitt-prefix model, enumerate every word of length at most two in

```text
raw, comb, raw*, comb*, x0, x1, z0, z1.
```

Exact rational group-algebra reduction gives

```text
max_g tau(F_cap g F_branch g*) = 1/16,               (QCS1)
```

while equality of the trace-quarter projections would require overlap
`1/4`.  No enumerated word conjugates one carrier to the other.  In fact the
maximum never exceeds the untransported statistically independent value
`tau(F_cap)tau(F_branch)=1/16`.

This first-moment statement does not mean the carriers commute.  The exact
second moment gives angle variance `1/64` and reflection-commutator energy
`1/2`, as recorded in
`two-pauli-quarter-carriers-have-fixed-reflection-holonomy`.

This is a bounded falsification result, not a no-conjugacy theorem for the
whole atlas group.  It rules out the cheapest possible repair: the missing
same-carrier bridge is not one raw/comb/Pauli generator or a product of two
such generators.  Any successful transport must use a genuinely longer
mixed rank-five word, a non-unitary packet compression, or the holonomy side
of `mixed-relations-force-holonomy-or-transverse-recovery`.
