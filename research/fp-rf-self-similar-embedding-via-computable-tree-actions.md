---
rg: 2
id: fp-rf-self-similar-embedding-via-computable-tree-actions
kind: route
title: Split the self-similar embedding into a tree-action hole and a self-similar Higman characterization
target: every-fp-rf-group-embeds-in-fp-self-similar-group
requires:
  - every-fp-rf-group-acts-on-a-regular-rooted-tree
  - fp-tree-groups-have-computable-faithful-tree-actions
  - computable-tree-groups-embed-in-fp-self-similar-groups
---

Let `G` be finitely presented and residually finite.

1. **A faithful action.** By
   [[every-fp-rf-group-acts-on-a-regular-rooted-tree]] there is `d >= 2` with
   `G <= Aut(T_d)`.
2. **A computable action.** By
   [[fp-tree-groups-have-computable-faithful-tree-actions]], `G` has a
   computable faithful action on `T_d`. Its word problem is solvable, by
   McKinsey or by the consequence clause of that claim.
3. **The overgroup.** By
   [[computable-tree-groups-embed-in-fp-self-similar-groups]], `G` embeds in a
   finitely presented self-similar group.

## Why this is a genuine split

- **Requirement 1 is necessary for the target.** Every self-similar group acts
  on a regular rooted tree. If requirement 1 fails, the target is refuted,
  through [[some-fp-rf-group-acts-on-no-regular-rooted-tree]].
- **Requirement 3 is established to be necessary for its own class.** Its
  hypotheses are exactly the properties of finitely generated subgroups of
  finitely presented self-similar groups. But its inputs are all finitely
  generated groups, so it can fail on a group that is not finitely presented
  without affecting the target.
- **Requirement 2 is established,** and it removes computability from the
  finitely presented case. For finitely presented inputs, the only structural
  question left between the target and requirement 3 is requirement 1.
