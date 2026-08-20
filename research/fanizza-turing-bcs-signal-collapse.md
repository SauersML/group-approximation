---
rg: 2
id: fanizza-turing-bcs-signal-collapse
kind: claim
title: The Fanizza Turing BCS has a polynomially certified signal-versus-error collapse
artifacts:
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
distinct_from:
  non-ce-bcs-has-finite-dimensional-forbidden-mass-gap: that compactness theorem forces forbidden mass in finite-dimensional exact-context models of one non-CE BCS; this is an effective machine-indexed family and bounds one distinguished projection in every approximately perfect strategy on the nonmember side.
  contractive-computation-ladder: that is an abstract scalar recurrence with a fixed contraction factor; the cited paper proves a polynomial relator decomposition and the final signal collapse, not that scalar recurrence verbatim.
---

For every recursively enumerable set `L` there is a computable family of
finite Boolean constraint systems `B_m`, computable positive integers `C_m`,
and a distinguished variable `x_D` with `D=(1-x_D)/2`, such that:

1. if `m in L`, the BCS algebra has a tracial state `tau` with `tau(D)>0`;
2. if `m notin L`, then for every `epsilon`-perfect strategy for the BCS game,
   its associated state satisfies

```text
phi(D) <= C_m epsilon.                                 (FTB1)
```

The nonmember proof contains projections and conjugated involutions obeying a
computation relation of the form

```text
P_tilde_n + X_tilde_n P_tilde_n X_tilde_n - P_tilde_(n+1)=0,
```

with a relator-ideal decomposition whose size is polynomial in the level `n`
for fixed machine index `m`.  Exponentially weighted summation of these
polynomial costs is what yields `(FTB1)`.

This is a quantitative signal-collapse theorem at the BCS strategy level.  It
does not by itself provide a finitely presented group, a group word detected
by `D`, or a separated nonhalting mark.
