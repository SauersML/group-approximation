---
rg: 2
id: three-gen-nonlinear-host-via-bilateral-recurrence
kind: route
title: Apply the bilateral scalar recurrence host to the absolute-exponential three-generator profile
target: three-gen-nonlinear-recurrence-lamp-has-simple-host
requires:
  - three-generator-recurrence-lamp-is-nonlinear
  - recurrence-nilpotent-lamps-have-simple-f-infinity-hosts
artifacts:
  - research/artifacts/beyond-polynomial-germs/recurrence-and-matrix-proofs.md
---

The first prerequisite identifies the source and proves all asserted
algebraic properties. Its profile `a^|n|` has forward tail `a^n` and
backward tail `a^(n+1)`, both integer recurrent. Add the constant
profile and apply the second prerequisite with `m=2`. The resulting
larger lamp/profile group contains `⟨A,X,T⟩`, so restricting its
faithful embedding gives the required host with the same two
finite-order generators. Infinite global profile rank is compatible
with the finite-rank endpoint lattices and is not suppressed by this
embedding. Both prerequisites are unresolved.
