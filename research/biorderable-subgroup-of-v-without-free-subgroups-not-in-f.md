---
rg: 2
id: biorderable-subgroup-of-v-without-free-subgroups-not-in-f
kind: claim
title: Some bi-orderable subgroup of Thompson's group V with no non-abelian free subgroup is isomorphic to no subgroup of F
distinct_from:
  klein-bottle-group-embeds-in-v-but-not-in-f: that group is torsion-free but not bi-orderable, so it answers only the numbered Problem 2.15; this claim asks for a bi-orderable witness
---

There is a group `G` that is isomorphic to a subgroup of Thompson's group `V`,
is bi-orderable, has no non-abelian free subgroup, and is isomorphic to no
subgroup of Thompson's group `F`.

This is the negative answer to
`zaremsky-2-15b-bi-orderable-subgroups-of-v-embed-in-f`.

## Attempts

- 2026-09-13 (z2-15b-biorderable). Candidates are bi-orderable solvable groups
  that fail a necessary condition for subgroups of `F`: the Heisenberg group,
  `BS(1,2)`, hyperbolic `Z^2 ⋊_A Z` with positive eigenvalues, and `Z ≀ Z^2`.
  Expected fates inside `V`:
  - the Heisenberg group, `BS(1,2)` and `Z^2 ⋊_A Z` should not embed in `V`
    either (germs at the finitely many attracting periodic points);
  - `Z ≀ Z^2` is undecided. Its wandering embeddings fail, because commuting
    elements of `V` act virtually cyclically on a common flow component. An
    abstract embedding whose lamps overlap is not excluded yet.
