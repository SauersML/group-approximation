---
rg: 2
id: kl-via-existentially-closed-overgroup
kind: route
title: Pass to an existentially closed overgroup and read off the solution
target: kervaire-laudenbach-nonsingular-conjecture
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Every group embeds in an existentially closed one, and an e.c. group solves
every finite system of equations and inequations over itself that can be
solved anywhere.  Since a nonsingular equation "ought" to be solvable, embed
the coefficient group in an e.c. overgroup, solve there, and the coefficients
have been preserved by construction.

Dead by `overgroup-room-does-not-supply-a-root`: "can be solved anywhere" is
the hypothesis, not a gift of the construction.  The system
`{ w(t) = 1 } ∪ { g != 1 : g in F }` is solvable in some extension exactly
when the elements of `F` survive in `G_w`, so existential closure hands back
precisely what it was asked to supply.

**What survives the demolition.**  Model-theoretic overgroups remain the
right place to *state* the conjecture — it is equivalent to a scheme of
consistency assertions about the coefficient diagram, and that reformulation
is occasionally clarifying.  What dies is the idea that closure properties
alone decide it.  The same warning applies to any "generic" or "universal"
overgroup construction whose solving power is defined by satisfiability.
