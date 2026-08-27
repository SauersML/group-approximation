---
rg: 2
id: atlas-a4-gl5-two-holonomy-readout
kind: claim
title: Collision 19243 pays the two-holonomy energy on every exact GL5 packet model
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
  - experiments/atlas-a4-gl5-two-holonomy-profile.json
distinct_from:
  atlas-a4-two-holonomy-reflection-energy-ceiling: that asks for a dimension-independent asymptotic estimate in arbitrary amplified regular A8 charts; this is an exact finite-rank calibration in the 31-point permutation representation of GL5(F2).
---

Embed `H=GL_4(F2)=A8` as `diag(GL_4(F2),1)` in `GL_5(F2)`, and let
`pi_31` be the permutation representation of `GL_5(F2)` on the thirty-one
nonzero vectors of `F2^5`.  Exhaust all `9,999,360` relative positions and
retain the `202` positions satisfying the thirty A4 packet relations exactly,
as in `atlas-a4-gl5-packet-collision-screen`.

For each retained relative position `U`, put

```text
c=hk,
a=zb,
E_2HOL(U)=2 delta_U(c)^2+delta_U(a)^2,
epsilon_q(U)=||q_19243(U)-1||_2,
```

using the canonical bridge labels of `atlas-t30-is-one-parabolic-c3-bridge`
and normalized Hilbert--Schmidt norm in `pi_31`.  Then every one of the 202
positions satisfies the exact inequality

```text
E_2HOL(U) <= 5 epsilon_q(U)^2.                         (GL5-2HOL-READOUT)
```

The constant `5` is sharp on this finite family: equality holds at exactly
`96` positions.  In integer units with denominator `31`, the only possible
collision squared defects are `32/31` and `48/31`, while the only possible
two-holonomy energies are

```text
96/31, 112/31, 128/31, 144/31, 160/31.
```

This strengthens the zero-set statement for the first rank enlargement: on
every exact packet stratum in this model, collision 19243 quantitatively pays
the entire two-holonomy energy.  It is not a proof of the amplified-regular
ceiling.  The 31-point permutation representation has fixed multiplicity and
does not see arbitrary matrix-valued Schur holonomy.
