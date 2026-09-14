---
rg: 2
id: cstar-simple-iff-amenable-subgroups-not-confined
kind: claim
title: "Kennedy: a countable group is C*-simple iff it has no non-trivial amenable URS, iff no amenable subgroup is confined"
---

**ESTABLISHED (import plus an elementary reformulation).**

Let `G` be a countable discrete group. The following are equivalent:
1. `C*_r(G)` is simple (G is C*-simple);
2. `G` has no non-trivial amenable uniformly recurrent subgroup;
3. the conjugacy class of every amenable subgroup `H ≤ G` accumulates at the trivial subgroup in the Chabauty space `Sub(G)`;
4. no amenable subgroup of `G` is confined. Here `H` is confined if some finite `P ⊆ G \ {1}` meets every conjugate
   `gHg^{-1}`.

(1)⟺(2)⟺(3) is the import. (3)⟺(4) is elementary: in `Sub(G)` the sets `{K : K ∩ P = ∅}`, for finite `P ⊆ G \ {1}`,
form a neighbourhood basis of `{1}`. So the conjugacy class of `H` accumulates at `{1}` iff every such `P` misses some
conjugate of `H`, i.e. iff `H` is not confined. The trivial subgroup is not confined, so (2) and (4) are consistent.

**Proof:** `cstar-simple-iff-amenable-subgroups-not-confined-citation`.
