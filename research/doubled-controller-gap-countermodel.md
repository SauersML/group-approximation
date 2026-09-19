---
rg: 2
id: doubled-controller-gap-countermodel
kind: route
title: Dress a gapped three-projection compressor by exact controller rotations
target: doubled-controllers-do-not-preserve-game-gap
requires: []
---

In an arbitrary marked-spin controller representation write

```text
c=(P_0+P_1r) tensor u,   h=H tensor v,
```

with multiplicity involutions `u,v` commuting with `r`.  For the doubled
word `B=(ch)^2`, put `w=(uv)^2`.  A direct two-by-two calculation gives

```text
P_0BP_0=P_0 tensor wQ,   Q=(I+r)/2.
```

Now take `K=C^3` and

```text
Q_1=proj span(e_1,e_2),
Q_2=proj span(e_2,e_3),
Q_3=proj span(e_3,e_1).
```

Their rejection energies average to `||xi||^2/3`, so the undressed
compressor has a fixed gap.  Choose `w_1` as a quarter-turn taking `e_1` to
`e_2` inside `Q_1K`, `w_2` taking `e_2` to `e_3` inside `Q_2K`, and `w_3=I`.
Each commutes with its `Q_j`, yet

```text
w_3Q_3w_2Q_2w_1Q_1 e_1=e_3,
```

so the dressed cyclic product has norm one.  Every planar quarter-turn is
`(uv)^2` for two reflections supported on the accepted space, making this an
exact controller model.

Conjugating the control projection by each doubled block cancels the
multiplicity factor, and the interleaved Hecke product recovers
`Q_m...Q_1`.  Those projections are additive corners, however, not one
ordinary unitary word.  This proves both the no-go and the precise salvage.
