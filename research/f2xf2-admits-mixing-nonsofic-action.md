---
rg: 2
id: f2xf2-admits-mixing-nonsofic-action
kind: claim
title: F2 x F2 has an essentially free mixing p.m.p. action that is not sofic
distinct_from:
  f2xf2-admits-nonsofic-action: that asks for any free nonsofic action of F2 x F2, with no mixing; this asks for a mixing one, which no Kun-Thom or co-induced action can be
  mixing-free-nonsofic-action-of-sofic-group: that asks for a mixing nonsofic action of some sofic group; this fixes the group F2 x F2
---

**OPEN.** `F_2 × F_2` admits an essentially free, mixing p.m.p. action that is not sofic
(Păunescu Definition 1.4). `F_2 × F_2` is residually finite, so this answers
`mixing-free-nonsofic-action-of-sofic-group`, and it implies `f2xf2-admits-nonsofic-action`.

## Attempts

* **From a lattice with locally infinitely transitive projections (live, conditional).**
  `f2xf2-mixing-nonsofic-action-from-infinitely-transitive-lattice` needs
  `nonsofic-infinitely-transitive-tree-lattice`. The transfer itself is the established
  `nonsofic-infinitely-transitive-tree-lattice-gives-mixing`.
* **From Radu's BMW lattice: dead as an induced action.** By
  `radu-lattice-induced-actions-are-never-mixing`, no product envelope, seed or cocompact
  lattice gives mixing, because the vertical closure of `Γ_R` is locally `C_2` and its
  horizontal kernel is infinite. What remains is an embedding of `Γ_R` in a lattice with
  locally `∞`-transitive projections
  (`radu-bmw-lattice-embeds-in-infinitely-transitive-tree-lattice`).
* **Kun--Thom Theorem C.** Needs an infinite Kazhdan subgroup, and `F_2 × F_2` is Haagerup.
  Its actions are never mixing in any case (`mixing-free-nonsofic-action-of-sofic-group`).
* **Păunescu class.** `f2xf2-in-paunescu-class`, if true, makes every action sofic and
  refutes this claim.
