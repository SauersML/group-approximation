---
rg: 2
id: binary-leavitt-unit-group-hyperlinear
kind: claim
title: The binary Leavitt unit group, the first nonsofic group, is hyperlinear
distinct_from:
  leavitt-steinberg-hs-unstable: that is a normalized-HS *stability* statement about the Steinberg cover St_5(L), which yields a hyperlinear nonsofic *central quotient* only through the stability fork; this asks directly whether the nonsofic group itself has Hilbert--Schmidt models, with no stability hypothesis and no cover
  openai-leavitt-unit-nonsofic: that is the established nonsoficity theorem for this group; this is the orthogonal approximation question about the same group, and the two are compatible -- their conjunction is exactly the Q3.4 separation
  hyperlinear-nonsofic-group: that asks for *some* hyperlinear nonsofic group; this pins the candidate to one now-explicit group, so it can be attacked with that group's structure rather than searched for
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

OPEN.  Does `L_{F_2}(1,2)^x` -- or its finitely generated nonsofic subgroup
`G = EL_D(R)` from `openai-leavitt-unit-nonsofic` -- admit normalized
Hilbert--Schmidt models?  Equivalently, is `L(G)` Connes embeddable?

## Why this question cannot have an uninteresting answer

Since 2026-08-01 there are unconditional nonsofic groups.  For any such `G`,
exactly one of the following holds, and each closes a root of this graph --
one of them the program goal:

```text
G hyperlinear      =>  hyperlinear nonsofic group      =>  q3-4-resolved (No)
G not hyperlinear  =>  the first nonhyperlinear group  =>  non-hyperlinear-group
```

Before 2026-08-01 no group was known to sit on either side of that fork, so
no single group could be a fork machine.  That is the structural change the
new nonsoficity theorems make, and it is why a decisive analytic verdict on
*one* explicit nonsofic group is now worth more than the same verdict on an
arbitrary candidate.  The same disjunction applies verbatim to
`kun-thom-nonsofic-wreath` and to Fournier-Facio's torsion-free examples
(arXiv:2608.02025); this node pins the first and best-understood one.

Note the asymmetry with the stability lane.  `leavitt-steinberg-hs-stability-fork`
is also a dichotomy over the same algebra, but it is mediated by normalized-HS
stability of the *cover* `St_5(L)` and reaches hyperlinearity only through a
central quotient.  The present question skips both mediations.

## Attempts

**Read it off the nonsoficity proof.**  Dead as stated: the nonsoficity proof
runs through one-sided compression `t Gamma t^{-1} <= Gamma` plus property (T)
plus a commuting non-LEF subgroup, and every step that kills permutation
models is a *refinement* argument that the trace cannot see.  This is the
whole content of `trace-blindness-sharpness` and of the `II_1` branch
surviving `invariant-size-collapse`: the compression mechanism is exactly the
one to which the normalized trace is blind.  So the mechanism that supplies
nonsoficity gives no signal in either direction here.

**Use the algebra facts already proved about this group.**  They do not
decide it.  `leavitt-unit-group-algebra-not-directly-finite` and
`leavitt-group-algebra-not-stably-finite` are genuine Kaplansky-type failures
in positive characteristic, and they are consistent with nonsoficity; but no
implication from hyperlinearity to direct finiteness in characteristic `p` is
known, so they refute nothing here.  Over `C` every group algebra is directly
finite via the trace on `L(G)`, so the complex case carries no information at
all.

**Build a model from the Leavitt structure.**  Not attempted here.  The
natural source is the tower of finite-rank corners; the obstacle is that the
defining Leavitt relations `t_i s_j = delta_{ij}`, `s_0 t_0 + s_1 t_1 = 1`
are exactly the relations of a non-stably-finite algebra, so an approximate
matrix model must break one of them by a `2`-norm-small amount while keeping
the group relations of `EL_D(R)` exact enough.  That is the same tension
`corner-renormalization-cost` measures.

**Deferred, deliberately.**  The negative half of the fork is not restated as
a separate claim here: it is already served by `leavitt-steinberg-stable-branch`
and by the direct routes into `non-hyperlinear-group`.
