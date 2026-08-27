---
rg: 2
id: parallel-shared-algebra-edge-holonomy-proof
kind: route
title: Compose two full structural edge intertwiners and apply forbidden-support saturation
target: two-edge-holonomy-erases-role-packed-payload
requires:
  - role-packed-bcs-gap-is-one-idempotent
  - agent-aggregate-escape-forbidden-support-saturation
  - agent-aggregate-escape-normalizer-erases-payload
---

The composition `V^*U` conjugates the source algebra by
`psi^(-1)phi`, so it is a normalizer.  Full reducing support of `QB_f` then
identifies its returned reducing hull with `WQW^*`.  When the two edge maps
agree, the holonomy lies in the commutant; if it also preserves `Q`, it fixes
`QB_f` and has full overlap.  Fixed finite-packet exactification gives the
same alternatives with `O(sqrt(E))` loss.
