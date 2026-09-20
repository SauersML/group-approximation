---
rg: 2
id: wave3-audit-symplectic-root-lift-proof
kind: route
title: Rank-two root commutators verify all eleven relators before taking central quotients
target: wave3-audit-symplectic-root-lift
requires:
  - cckw-ghb2-kms-group-structure
  - wave3-canonical-k7-class-has-primitive-evaluation
artifacts:
  - research/artifacts/hyperbolic-rf-wave3-symplectic-lift-2026-09-20.md
---

Write alpha=e1+e2, beta=e2-e1, gamma=-2e2. Root additivity gives
the three seventh powers. The Chevalley commutator relations give

```
[U_alpha,U_beta] <= U_(2e2),
[U_gamma,U_alpha] <= U_(e1-e2) U_(2e1),
[U_gamma,U_beta] <= U_(-e1-e2) U_(-2e1).
```

The first right-hand root group commutes with U_alpha and U_beta.
The two factors in each remaining right side commute with U_gamma.
Each of the latter pairs generates a group of nilpotency class at
most three: commuting a height-two root once more can only produce
the height-three root, which is central in that subsystem. This
proves all two length-three (a,b) relations, both repeated-c
length-three relations, and all four length-four relations.

No inference from a possibly noninjective global Steinberg map is
used: these are relations inside the Steinberg presentation itself.
The resulting lift restricts to K7. Composing it with any morphism
from the Steinberg preimage of Q to a central extension of Q gives
a splitting after pullback to K7. Primitivity of c0 shows its mod-m
evaluation is nonzero, excluding that class. Equivalently the
central generator of its integral cover lies in the commutator
subgroup and is killed by the difference of a cover map and the
exact lifted base map.
