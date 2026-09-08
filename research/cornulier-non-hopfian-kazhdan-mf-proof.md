---
rg: 2
id: cornulier-non-hopfian-kazhdan-mf-proof
kind: route
title: Apply the central-quotient theorem to the imported linear presentation
target: cornulier-non-hopfian-kazhdan-groups-are-mf
requires:
  - cornulier-kazhdan-groups-are-central-quotients-of-linear-groups
  - central-quotients-of-residually-finite-groups-are-mf
  - kazhdan-defects-vanish-in-central-quotients-of-rf-groups
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

## Why sufficient

The first prerequisite writes each member of the family as `Gamma/Z` with
`Gamma <= GL_r(Z[1/p])` and `Z <= Z(Gamma)`, and proves `Gamma` residually
finite by reduction modulo an auxiliary prime.  A finitely generated
linear group is countable, so `Gamma` satisfies the hypotheses of the
other two prerequisites verbatim.

The second gives MF; the third gives `(CN2)` for every property-(T)
subgroup.  No further input is needed, and nothing about non-Hopficity,
finite presentability or the outer automorphism group enters the
derivation — those are what make the family an attractive candidate, not
what makes the argument work.

## Scope

The conclusion is about the members of the family themselves.  It says
nothing about groups constructed over them; in particular a wreath product
`B^(X) semidirect H` built from such a group is not a central quotient of a
residually finite group, and the sofic non-MF constructions that use a
Kazhdan self-embedding are unaffected.
