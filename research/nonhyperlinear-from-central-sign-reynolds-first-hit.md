---
rg: 2
id: nonhyperlinear-from-central-sign-reynolds-first-hit
kind: route
title: Feed central-sign forbidden Reynolds mass into the first-hit reservoir floor
target: non-hyperlinear-group
requires:
  - central-sign-bcs-atoms-are-subgroup-reynolds-projections
  - central-sign-reynolds-atoms-have-fixed-canonical-density
  - subgroup-hecke-hnn-is-a-regular-safe-rank-actuator
  - central-sign-reynolds-first-hit-compiler
  - non-ce-bcs-has-robust-approximate-energy-gap
  - branching-plus-first-hit-exits-forces-hs-floor
---

Exactify each fixed elementary-abelian context packet.  Identity `(CSR1)`
identifies every assignment atom with an ordinary subgroup Reynolds
projection, and `(CSD1)` gives each chosen atom a fixed positive canonical
carrier density.  The robust non-CE BCS gap is used only inside the compiler
to distinguish finite matrix multiplicity from the regular compensation
flow.  The compiler turns that matrix-only distinction into persistent active
carriers and orthogonal first-hit exits while retaining an exact infinite
completion.

Choose the fixed depth `N` with `eta N q_*>1`.  Then
`branching-plus-first-hit-exits-forces-hs-floor` gives a dimension-independent
positive lower bound on presentation error, contradicting a canonical
hyperlinear microstate sequence.
