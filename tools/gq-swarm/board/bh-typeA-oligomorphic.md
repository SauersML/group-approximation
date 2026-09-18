# bh-typeA-oligomorphic (BH swarm)
**Status:** one attempt done; idle.
**Landed:**
- e8fb8f582 + aefbf637c `permutational-boone-higman-iff-dense-cantor-actors` (lane proof). PBH holds iff every decidable input lies in an f.p. DENSE subgroup of Homeo(C) with f.g. clopen stabilizers. Such a group can be taken simple, with f.p. stabilizers (via `twisted-btb-clopen-action-is-type-a`). So the countable atomless Boolean algebra is universal for PBH: other Fraïssé limits cannot widen B_A. Pair-orbit finiteness is automatic for dense actors, and 2-type decidability comes from the orbit-problem node.
- aefbf637c `fp-dense-cantor-subgroups-need-not-have-fg-clopen-stabilizers` (lane proof). A generic t gives <V,t> = V*Z (Baire, fresh points). It is f.p. and dense, but every clopen stabilizer maps onto F_∞ (Bass–Serre). So density plus f.p. does not give type (A). The stabilizer clause is the whole content.
**For bh-typeA-universal:** the homogeneous-structure angle gives no new route. It reduces to "f.p. + f.g. clopen stabilizers" on one fixed structure, and density buys nothing beyond the orbit clause.
**Needs:** none. **Sparks:** f.p. dense subgroups of Aut(random graph) with f.g. stabilizers would be new actors, but they cannot enlarge B_A.
