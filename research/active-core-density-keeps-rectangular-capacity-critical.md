---
rg: 2
id: active-core-density-keeps-rectangular-capacity-critical
kind: claim
title: Positive-density reblocking does not make the nested Leavitt capacity strict
distinct_from:
  torsion-normal-generator-has-full-support-corona-core: that guarantees a positive-density marked carrier after reblocking; this proves that density alone does not constrain its internal label-versus-multiplicity profile.
  dual-prefix-renyi2-rate-is-critical-under-rectangular-escape: that proves criticality as an information-rate statement; this gives the direct finite rank/cross-Gram capacity countermodel inside a full active core.
---

**ESTABLISHED FIREWALL.**  Fix any depth `N` and any positive density
`beta<=1`.  There are finite matrix packet models on a projection `P` with
`tau(P)>=beta` in which every nested binary Pauli table through depth `N` is
exact and

```text
P M_d P ~= M_(2^n) tensor M_(m_n),
m_n=2m_(n+1),                                         (PAC1)
```

for `0<=n<N`.  The total carrier rank `2^n m_n` is constant.  Each binary
refinement therefore uses exactly the full doubled target capacity, and the
capacity lower bound for two incoming branches is an equality.  Their ranges
may be orthogonal, so no positive cross-Gram mass is forced.

The model can occupy the entire active core (`P=1`) or be tensored with an
arbitrary spectator block to realize any fixed rational density.  Hence the
rank comparison

```text
rank(p_mark) <= rank(P) <= L rank(p_mark)              (PAC2)
```

from `torsion-normal-generator-has-full-support-corona-core` does not change
the conclusion.  Reblocking removes dilution of a defect after it has been
found; it does not create a strict capacity deficit inside a coherent
rectangular packet.

Nor does fixed-depth rank integrality help.  Taking `m_0` divisible by
`2^N` realizes `(PAC1)` exactly, and common amplification preserves both
the active density and every normalized trace.  Since `N` is fixed before a
microstate coordinate, the multiplicity can always absorb that divisibility.

Consequently the positive cross-Gram leaf
`binary-leavitt-native-two-scale-cross-gram-positive` cannot be closed by
active-core density, finite depth, or integer rank granularity alone.  A
successful proof must add a row that makes the reproduction number strictly
larger than one on the **same named target**, or directly couples the two
orthogonal rectangular ranges.

