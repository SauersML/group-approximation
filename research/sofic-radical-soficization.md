---
rg: 2
id: sofic-radical-soficization
kind: claim
title: The sofic radical is the kernel of soficization
distinct_from:
  sofic-radical-linear-action-criterion: That recognizes membership of one marked word in the radical from finite actions; this identifies the radical as a whole with the smallest normal subgroup having sofic quotient.
  radical-collision-criterion: That converts one radical element plus one hyperlinear detector into a separating group; this is the structural description of the radical itself, with no hyperlinear input.
  kun-thom-clifford-radical-phase: That exhibits one explicit word in the sofic radical of one explicit group and its Clifford detector; this is a general structure theorem about the radical of an arbitrary countable group and names no group.
  simple-sofic-total-mf-radical: That concerns the MF radical, which is total for a specific simple sofic group; this concerns the sofic radical, which for that same group is trivial precisely because it is sofic.
---

Write `Rad_sof(H)` for the intersection of the kernels of all homomorphisms
from a countable group `H` to sofic groups.  Then:

1. **Functoriality.**  Every homomorphism `phi:H->Q` satisfies
   `phi(Rad_sof(H)) <= Rad_sof(Q)`.
2. **Sofic quotient.**  `H/Rad_sof(H)` is sofic; equivalently `Rad_sof(H)`
   is the smallest normal subgroup of `H` with sofic quotient.
3. **Detection of nonsoficity.**

```text
H is sofic   <==>   Rad_sof(H)=1.
```

Consequently a nontrivial sofic radical is not a rarer or more special
phenomenon than nonsoficity: they are the same phenomenon.  Every nonsofic
group supplies sofic-radical elements, and no group outside that class
supplies any.
