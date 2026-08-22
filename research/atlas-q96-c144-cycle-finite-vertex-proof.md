---
rg: 2
id: atlas-q96-c144-cycle-finite-vertex-proof
kind: route
title: Unite the four marked finite-vertex presentations and screen their colimit
target: atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test
requires:
  - atlas-forward-core-triangle-has-faithful-q96-completion
  - atlas-forward-collision-bass-serre-reduction
artifacts:
  - experiments/atlas_a4_q96_c144_cycle_low_index.g
  - research/artifacts/atlas-a4-q96-c144-cycle-screen.json
---

The `F'` relations in `(Q96-C-2)` split its generators into the commuting
dihedral pairs `<r,u>` and `<z,c>`, each of order six.  The `Q` relations are
exactly the certified order-96 presentation.  For `J`, the collision quotient

```text
<t,s,c | t^3,s^2,c^2,(st)^2,(ct)^3,q>
```

has order `24` by exact Todd--Coxeter enumeration, with `<t,s>~=S3` and
`<c,t>~=A4`; hence it is the marked `S4`.  Finally the last two cubes together
with `<r,z,b>` are the established order-144 forward-fan presentation.

Identifying equally named edge generators and applying the universal property
of presentations gives `(Q96-C-2)`.  In any permutation quotient, closure of
the four displayed generator subsets computes whether each finite vertex
injects.  The verifier reports a survivor exactly when the four orders are
`[36,96,24,144]`.  The stored timeout record makes no assertion about the
unreturned list.
