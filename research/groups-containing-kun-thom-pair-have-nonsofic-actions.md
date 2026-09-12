---
rg: 2
id: groups-containing-kun-thom-pair-have-nonsofic-actions
kind: claim
title: Every group containing an infranormal non-normal Kazhdan pair has a free nonsofic p.m.p. action
distinct_from:
  kun-thom-free-nonsofic-action: that is the free nonsofic action of the ambient group G of one pair; this is the same conclusion for every countable group that merely CONTAINS such a pair, obtained by co-induction
  sofic-action-class-closed-under-commensurability: that is the general permanence theorem for Paunescu's class; this is its instantiation at the Kun--Thom obstruction
---

**ESTABLISHED.** Let `L` be a countable group containing subgroups `Γ <= G <= L`
such that `Γ` is infranormal and not normal in `G` and both `Γ` and `G` have
property (T). Then `L` is not in Păunescu's class `𝒮`, and `L` admits an
essentially free p.m.p. action that is not sofic.

Explicitly, with `Z` the free ergodic nonsofic `G`-action of
`kun-thom-free-nonsofic-action` (generalized Bernoulli over `G/Γ` times the
Bernoulli shift of `G`),

```text
X_L = CoInd_G^L(Z) × ({0,1},fair)^L       (diagonal L-action)
```

is essentially free and not sofic.

Instances: every countable group containing
`EL_r(F_q[x_1^(±1),...,x_d^(±1)]) ⋊ SL_d(Z)` for some prime power `q` and
`r, d >= 3` (Kun--Thom Theorem E). With
`sofic-action-class-closed-under-commensurability`, the same holds for every group
commensurable with a group that contains such a pair.

**What this does not give.** It gives no ergodicity of `X_L` (co-induction was
not analysed for that) and no nonsofic action of a group that contains no such
pair. `sl3z-admits-nonsofic-action` records one lattice where no pair is known.
