---
rg: 2
id: positive-cross-gram-state-rounds-to-common-pvm
kind: claim
title: A positive-cross-Gram state rounds two packets to one common PVM
artifacts:
  - research/artifacts/lin-state-local-cross-gram-exactification-2026-08-23.md
distinct_from:
  one-gram-vector-decodes-a-finite-bcs-strategy: that obtains the game gap directly from one Gram vector and needs no rounding; this supplies a reusable common finite-packet corner for subsequent exactification or mixed-word analysis.
  pairwise-cross-grams-do-not-supply-one-game-state: that allows a different Gram on every edge; this assumes one fixed positive-mass Gram operator for the complete packet.
  forty-two-branch-gram-polar-rounding: that orthogonalizes one nearly orthogonal family using its total Gram overlap; this aligns two already-projective packets in one state-dependent positive corner.
  two-transport-cross-gram-has-a-fixed-mass-reducing-corner: that cuts the cross-Gram square into an approximately reducing source projection; this performs the subsequent measurement-level rounding of both PVM packets.
  labelled-pvm-branch-gram-gives-lin-corner: that proves exact labelled-block support, mass, and source-commutator identities; this states the general two-PVM rounding consequence on the resulting Gram state.
---

Let `(P_a^x)_a` and `(Q_a^x)_a` be two finite PVM packets and let `G` be a
contraction with

```text
m=||G||_2^2>=m_0>0,
E=E_x sum_a||P_a^xG-GQ_a^x||_2^2.                     (PCR1)
```

After polar-gauging the second packet, there are a projection `R` and one
PVM packet `(C_a^x)` on `R` such that

```text
tau(R)>=m_0/2,
E_x sum_a||(P_a^x-C_a^x)R||_2^2
 +E_x sum_a||(Qtilde_a^x-C_a^x)R||_2^2
 <=O_(m_0)((E/m)^(1/4)).                              (PCR2)
```

In particular `E=o(m)` yields one fixed-density packet corner shared by
both sides. For orthogonal labelled source and target projections, the
single block contraction

```text
G=sum_i F_iT_iE_i
```

is contractive and satisfies `F_iG=GE_i` identically, so label
synchronization contributes zero to `(PCR1)`. Only fixed mass and the
genuinely mixed/root/return covariance on this same `G` remain.
