---
rg: 2
id: atlas-packet-collision-m2-has-full-coefficient-algebra
kind: claim
title: The exact multiplicity-two packet-collision escape has full coefficient algebra, and q14 is its first blocker
artifacts:
  - experiments/atlas_a4_repeated_module_escape_verify.py
distinct_from:
  atlas-multiplicity-two-packet-collision-hub-escape: that verifies the packet and collision words and shows q14 fails; this computes the Morita coefficient algebra of the same witness.
  atlas-q14-exact-allows-full-coefficient-cyclicity: that gives full coefficient algebras with q14 exact but asserts no packet or collision relations; this gives packet and collision exact but fails q14.
  atlas-left-ideal-rank-nonwandering: that is an asymptotic growing-multiplicity statement; this is a sharp multiplicity-two calibration and its direct amplifications have positive-density minimal seeds.
---

ESTABLISHED.  Let

```text
T=401004080301c030 in GL_8(F2)                        (PCM1)
```

be the multiplicity-two relative chart frame from
`atlas-multiplicity-two-packet-collision-hub-escape`, in the interleaved
`F2^4 tensor F2^2` basis.  That witness satisfies all twelve distinct packet
pair-cubes and collision `19243` exactly, while q14 is nonidentity.

Write `T=(T_ia)` and `T^(-1)=(S_bj)` in `4 by 4` blocks over `M_2(F2)`.
Then four coefficient products are

```text
T_(1,3) S_(3,1)=E_(1,1),
T_(1,3) S_(1,2)=E_(1,2),
T_(1,4) S_(3,1)=E_(2,1),
T_(1,4) S_(1,2)=E_(2,2).                             (PCM2)
```

Therefore its multiplicity coefficient algebra is

```text
C_T=M_2(F2).                                          (PCM3)
```

This determines exactly which side of the augmented packet first blocks the
known full-coefficient stratum: the packet cubes do not, collision does not,
and q14 does reject this witness.

The direct amplification `T tensor I_k` is not a growing-width countermodel.
Its coefficient algebra is `M_2(F2) tensor I_k` on `F2^2 tensor F2^k`.
Every cyclic seed for that algebra has multiplicity-coordinate dimension at
least `ceil(k/2)`: one seed vector has only two `F2^k` coordinate vectors,
and matrix multiplication on the first factor cannot enlarge their span.
Thus its minimal seed density is at least `1/4`, not `o(1)`.
The remaining enemy must mix the amplification coordinates genuinely rather
than repeat this exact escape block.
