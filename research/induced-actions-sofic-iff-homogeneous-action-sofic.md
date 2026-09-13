---
rg: 2
id: induced-actions-sofic-iff-homogeneous-action-sofic
kind: claim
title: Induction from a lattice through its envelope preserves soficity of every seed exactly when the homogeneous action of the lattice is sofic
distinct_from:
  howe-moore-lattice-nonsofic-action-transfers-to-mixing: that shows induction carries nonsofic seeds to nonsofic mixing witnesses; this shows it carries sofic seeds to sofic witnesses iff the one homogeneous action Gamma on H/Gamma is sofic
  paunescu-class-is-measure-equivalence-invariant: that moves nonsoficity along arbitrary couplings; this isolates the seed-free part of the canonical coupling H as the only possible source of nonsoficity in induced actions
---

**ESTABLISHED (unreviewed).** Let `H` be a locally compact second countable group, `Γ <= H` a lattice,
and suppose the left action `Γ ↷ H/Γ` (Haar probability measure) is essentially free. Then the
following are equivalent:

1. `Γ ↷ H/Γ` is sofic (Păunescu Definition 1.4);
2. for every sofic p.m.p. action `Γ ↷ Z` (the trivial one-point action included), the restriction to
   `Γ` of the induced action `H ↷ H ×_Γ Z` is sofic.

Consequences.

* **The homogeneous action is the unit of the transfer.** If it is sofic, induction through `H`
  neither creates nor destroys soficity. By `howe-moore-lattice-nonsofic-action-transfers-to-mixing`,
  the induced witness `H ×_Γ Z'` is nonsofic iff the seed `Z` is. If it is not sofic, it is itself a
  nonsofic action of `Γ`. For a Howe--Moore envelope it is also mixing.
* **`SL_3(Z)`.** For `H = SL_3(R)`, `Γ = SL_3(Z)`, the action on `SL_3(R)/SL_3(Z)` is essentially free.
  The fixed set of `γ != 1` is a countable union of translates of proper centralizers, a Haar null set.
  `sl3z-lattice-space-action-is-not-sofic` was exactly the failure of 1 for this pair, and it is refuted.
  Condition 1 holds (`sl3z-lattice-space-action-is-sofic`, through equidistributed Hecke orbits). So for
  `SL_3(Z) <= SL_3(R)`, sofic seeds give sofic induced actions, and by
  `howe-moore-lattice-nonsofic-action-transfers-to-mixing` nonsofic ergodic seeds give nonsofic ones.

Proof in `induced-actions-sofic-iff-homogeneous-action-sofic-proof`.
