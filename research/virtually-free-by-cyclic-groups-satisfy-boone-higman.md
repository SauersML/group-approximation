---
rg: 2
id: virtually-free-by-cyclic-groups-satisfy-boone-higman
kind: claim
title: Every group with a finitely generated free-by-cyclic subgroup of finite index embeds in a finitely presented simple group
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that covers finitely generated free-by-cyclic groups themselves; this covers every group containing one with finite index, which a plain embedding theorem does not pass to.
  boone-higman-type-a-class-closed-under-finite-extensions: that is the permanence of the type (A) class under finite-index overgroups; this applies it to free-by-cyclic inputs.
  one-relator-groups-satisfy-boone-higman: that asks for all one-relator groups; this settles only those that are virtually finitely generated free-by-cyclic, among them the torsion-free two-generator virtually RFRS ones.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

**ESTABLISHED.** Let `G` have a subgroup of finite index isomorphic to
`F_k ⋊_φ Z` for some finite `k >= 0` and some `φ ∈ Aut(F_k)`. Then `G` embeds in
a finitely presented simple group.

**Credit.** This is an immediate combination of two known facts:
- Bux--Llosa Isenrich--Wu, Remark 12.7
  (`free-generalized-bs-groups-have-type-a-overgroups`);
- Zaremsky, arXiv:2405.18354, Proposition 5.6, closure of the permutational
  class under commensurability
  (`boone-higman-type-a-class-closed-under-finite-extensions`).

No novelty is claimed beyond recording the combination. The proof is
`virtually-free-by-cyclic-bh-proof`.

## Consequence for one-relator groups

Linton--Nyberg-Brodda, arXiv:2501.18306, Theorem 2.5.34, read on MSI: "If G is a
torsion-free two-generator one-relator group that is virtually RFRS, then G is
virtually {finitely generated free}-by-cyclic." So every torsion-free
two-generator one-relator group that is virtually RFRS satisfies Boone--Higman.

**What this does not reach.** Finitely generated free-by-cyclic groups are
residually finite. So this reaches no non-residually-finite one-relator group,
such as `BS(2,3)` or the Baumslag--Gersten group. `BS(2,3)` is covered separately
by Bux--Llosa Isenrich--Wu; the Baumslag--Gersten group is not covered by any
theorem imported here (`baumslag-gersten-base-is-elliptic-in-every-tree-action`).
