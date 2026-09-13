---
rg: 2
id: thompson-f-is-quasi-isometric-to-thompson-t
kind: claim
title: Thompson's group F is quasi-isometric to Thompson's group T
distinct_from:
  thompson-f-is-not-quasi-isometric-to-thompson-t: that is the opposite answer to the same sub-question; this is the unexpected answer, which would make F non-amenable.
---

**OPEN.** Thompson's group F with a word metric is quasi-isometric to Thompson's
group T with a word metric. This is the yes-answer to part (c) of Zaremsky
Problem 2.4 (`thompson-f-qi-to-thompson-t-resolved`).

A proof would also show that F is not amenable
(`thompson-f-nonamenable-if-qi-to-thompson-t`) and would answer part (f) yes,
since a quasi-isometry is a quasi-retraction.

## Attempts

- **No construction known.** F is the stabilizer of the base point in T, of
  infinite index, so neither inclusion is coarsely surjective. A quasi-isometry
  would have to reorganize T's cosets of F (indexed by the dyadic points of the
  circle) into F. The natural retraction `g ↦ R_{-g(0)} ∘ g` onto F is not coarsely
  Lipschitz (see `thompson-t-quasi-retracts-onto-f-resolved`). Where it stands: no
  approach.
