---
rg: 2
id: type-a-action-gives-boone-higman-for-subgroups
kind: claim
title: Every subgroup of a group carrying a type (A) action has solvable word problem and embeds in a finitely presented simple group
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that is the finite-presentability equivalence for the twisted Brin-Thompson group itself, a statement about SV_G; this is the downstream embedding payoff, a statement about every SUBGROUP of the acting group, and it is what a Boone-Higman route actually consumes. The criterion is the hypothesis of this one, not a restatement of it.
  boone-higman-conjecture: that is the open universal statement over all finitely generated groups with solvable word problem; this is a theorem that applies only to groups already known to sit inside an actor with a type (A) action, and supplies no such actor.
  boone-higman-thompson-simple-envelope: that produces a computably presented simple envelope from a solvable word problem and is a universal theorem; this produces a finitely PRESENTED simple envelope but only for the subgroups of a group given with a type (A) action, so it is conditional on an input the other theorem does not need.
  simple-envelope-forces-solvable-word-problem: that is the converse direction of Boone-Higman and derives decidability FROM a finitely presented simple envelope; this derives both decidability and the envelope from a permutation action, and its decidability half is a corollary rather than the point.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Call an action of a group `G` on a set `S` **of type (A)** when

1. the action is faithful,
2. `G` is finitely presented,
3. `Stab_G(s)` is finitely generated for every `s in S`,
4. there are finitely many `G`-orbits of two-element subsets of `S`.

Then every subgroup of `G` has solvable word problem and embeds in a finitely
presented simple group.

**Verification status.**  Read from source 2026-08-24.  Zaremsky, *Finite
presentability of twisted Brin--Thompson groups*, arXiv:2405.18354, states the
four conditions verbatim as

> "(A): The action is faithful, the group `G` is finitely presented, each
> `Stab_G(s)` for `s in S` is finitely generated, and there are finitely many
> `G`-orbits of two-element subsets of `S`."

its Theorem A verbatim as

> "Let `G` be a group acting faithfully on a set `S`.  Then the twisted
> Brin--Thompson group `SV_G` is finitely presented if and only if the action
> of `G` on `S` is of type (A)."

and its Corollary B verbatim as

> "Any subgroup of a group admitting an action of type (A) has solvable word
> problem and satisfies the Boone--Higman conjecture."

## Why the graph carries this and not only the criterion

`twisted-brin-thompson-finite-presentation-criterion` already carries Theorem
A.  Corollary B is a separate import because it packages the two steps a
route would otherwise have to redo by hand -- simplicity of `SV_G` under
faithfulness, and the containment `G <= SV_G` -- and because it hands the
conclusion to **subgroups**, which is what every embedding route needs: the
group one starts from is never the actor, it is something sitting inside the
actor.

The decidability half is not decoration.  It is the reason a type (A) action
is not free to construct: producing one over a group with unsolvable word
problem is impossible, so any construction of such an action must consume a
decidability hypothesis somewhere.  That consequence is drawn out as
`compilers-cannot-drop-the-decidability-hypothesis`.
