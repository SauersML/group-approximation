---
rg: 2
id: thompson-f-not-amenable-via-rotation-cosets-of-thompson-t
kind: route
title: Show that some finite set of elements of F cannot be twisted by dyadic rotations into an amenable subgroup of T; since amenability of F would make every such twist possible, F is nonamenable
target: thompson-f-is-not-amenable
requires:
  - thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive
  - jz-question-5-for-thompson-t-implies-f-nonamenable
---

**Route.** By item 3 of `jz-question-5-for-thompson-t-implies-f-nonamenable` (Step 3 of its proof), if `F` is
amenable then `T ↷ T/R_D` is locally amenably transitive, with `H = F` for every finite set. The prerequisite
`thompson-t-dyadic-rotation-cosets-are-not-amenably-transitive` says it is not. Hence `F` is not amenable.

**Why this is a decomposition.** The prerequisite is at least as strong as the target and can fail on its own:
if every finite `S ⊆ F` has a rotation twist generating an amenable subgroup of `T`, the prerequisite is false
whatever the truth of the root, and then Juschenko–Zheng's Question 5 fails for the finitely presented group
`T`. The regular `F`-set, where the analogous statement is equivalent to the root
(`liouville-action-criteria-cannot-decide-thompson-f-amenability`, item 2), has no twists; the dyadic rotations
are the extra freedom that separates the two.
