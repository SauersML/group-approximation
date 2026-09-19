---
rg: 2
id: leavitt-corner-nielsen-normal-form-proof
kind: route
title: Expand bridge letters in the two coefficient copies and forbid every complete boundary cancellation
target: leavitt-corner-subgroup-is-v4-v4-f2
requires: []
---

Expand `h_1=q_0p_1` and `k_2=p_0e_1` in the free-product normal form of
`G_0*G_1`.  At a boundary with `V_4(h_0,h_2)`, complete cancellation would
put `q` or `p` in `<a,e>`; at a boundary with `V_4(k_0,k_1)`, it would put
`p` or `e` in `<a,q>`.  Root support and the nontrivial permutation part
exclude all four memberships.

Within a reduced word in the two bridge generators, the only same-copy
merges outside an inverse pair are `pe`, `ep^(-1)`, `qp`, and
`p^(-1)q`.  Each is nonidentity because the cycle permutation is distinct
from the elementary unipotents.  No whole syllable disappears, so the
expanded word remains a nonempty alternating normal form.  This proves the
embedding.
