---
rg: 2
id: type-a-actors-have-no-infinite-virtually-central-subgroup
kind: claim
title: A group acting faithfully with finitely many orbits on two-element subsets has no infinite subgroup whose centralizer has finite index; in particular its center is finite
distinct_from:
  type-a-action-gives-boone-higman-for-subgroups: that is the payoff of a type (A) action, simple envelopes for every subgroup of the actor; this is a necessary condition on the actor itself, which rules out actors with an infinite virtually central subgroup.
  fp-full-binary-cantor-groups-have-type-a-actions: that supplies type (A) actions for finitely presented full Cantor groups containing V; this constrains which groups can carry any such action at all.
  deligne-lattice-embeds-in-no-rover-nekrashevych-group: that excludes Rover--Nekrashevych hosts for Deligne's lattice through property (T); this excludes Deligne's lattice, and every group with infinite center, as its own type (A) actor, with no use of property (T).
artifacts:
  - research/artifacts/ideas-2026-09-13/bh/bh-pbh-separation.md
---

**ESTABLISHED** through `type-a-actors-have-no-infinite-virtually-central-subgroup-proof`
(elementary; no novelty claimed).

**Statement.** Let a group `E` act faithfully on a set `S` with finitely many
`E`-orbits of two-element subsets of `S`. Let `Z <= E` be a subgroup whose
centralizer `C_E(Z)` has finite index in `E`. Then `Z` is finite.

**Corollaries.**
1. `Z(E)` is finite.
2. No element of infinite order in `E` has finitely many conjugates.
3. Condition 4 of a type (A) action (`type-a-action-gives-boone-higman-for-subgroups`)
   is exactly the hypothesis above. So a group with an infinite central subgroup,
   or more generally an infinite subgroup with finite-index centralizer, carries
   no action of type (A).
4. **Deligne's lattice.** The preimage `Gamma~` of `Sp_2n(Z)` (`n >= 2`) in the
   universal cover of `Sp_2n(R)` has infinite center
   (`deligne-universal-cover-lattice-is-non-rf-kazhdan`, item 1). So `Gamma~` has
   no type (A) action. If `Gamma~ <= E` and `E` carries a type (A) action, then
   the generator of `Z(Gamma~)` has infinitely many `E`-conjugates.

**Scope.** This constrains the actor, not the input. It says nothing against
embedding a group with infinite center inside some other type (A) actor where
that center stops being virtually central.
