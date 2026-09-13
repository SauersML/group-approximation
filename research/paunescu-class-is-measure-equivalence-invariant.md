---
rg: 2
id: paunescu-class-is-measure-equivalence-invariant
kind: claim
title: Paunescu's class of groups with only sofic actions is invariant under measure equivalence
distinct_from:
  sofic-action-class-closed-under-commensurability: that covers subgroups and finite-index overgroups; this covers measure equivalence, which contains commensurability and all lattices of one locally compact group but not arbitrary subgroups
  paunescu-sofic-action-class-permanence: that imports the families Paunescu proved to lie in the class; this proves that membership depends only on the measure equivalence class
  groups-containing-kun-thom-pair-have-nonsofic-actions: that transfers nonsoficity to overgroups by co-induction; this transfers it along measure equivalence couplings
artifacts:
  - research/artifacts/paunescu-class-measure-equivalence-2026-09-12.md
---

**ESTABLISHED (unreviewed).** Let `𝒮` be Păunescu's class of countable groups all
of whose p.m.p. actions are sofic (Definition 3.2 of arXiv:1002.0605; soficity as
in Definition 1.4). If `G ∈ 𝒮` and `H` is measure equivalent to `G`, then `H ∈ 𝒮`.

Explicitly: if `G ↷ Z` is a nonsofic p.m.p. action and `Ω` couples `G` with `H`,
then with `B` the Bernoulli shift of `G × H`, the action of `H` on
`(Ω × Z × B)/G` is essentially free and nonsofic.

**Consequences.**

1. **Lattices.** For a lcsc group `L`, either every lattice of `L` lies in 𝒮 or
   none does.
2. **Products of two trees.** For `p, q >= 3`, a cocompact lattice in
   `Aut(T_p) × Aut(T_q)` lies in 𝒮 iff `F_2 × F_2 ∈ 𝒮` (artifact 4.2, through the
   lattice `C_2^(*p) × C_2^(*q)` and commensurability). So `F_2 × F_2 ∈ 𝒮` would
   imply that Radu's BMW lattice (`radu-bmw-lattice-sofic`) and every other such
   lattice is sofic. One nonsofic such lattice would give `F_2 × F_2` a free
   nonsofic action.
3. **SL_3(Z).** `sl3z-admits-nonsofic-action` has the same answer for every
   lattice of `SL_3(R)`.
4. **Kun--Thom groups.** Every group measure equivalent to a group containing an
   infranormal non-normal Kazhdan pair lies outside 𝒮.

**Where credit sits.** Subgroup closure of 𝒮 is Alpeev, arXiv:1706.01864,
Theorem 5.2, and treeable groups lie in 𝒮 by his Theorem 5.1. A bounded search
(four web queries; Păunescu 2011, Cordeiro 2016, Alpeev 2017, Bowen--Burton 2021)
found no statement of measure equivalence invariance. It may be folklore.

Proof in `paunescu-class-me-invariance-proof`.
