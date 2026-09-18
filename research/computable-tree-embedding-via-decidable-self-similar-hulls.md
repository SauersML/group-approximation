---
rg: 2
id: computable-tree-embedding-via-decidable-self-similar-hulls
kind: route
title: Split the self-similar Higman characterization into a finitely generated self-similar hull with solvable word problem and a Higman step for such hulls
target: computable-tree-groups-embed-in-fp-self-similar-groups
requires:
  - computable-tree-groups-embed-in-decidable-fg-self-similar-groups
  - decidable-fg-self-similar-groups-embed-in-fp-self-similar
---

Let `H` be finitely generated, with solvable word problem and a computable
faithful action on a regular rooted tree.

1. **The hull.** By
   [[computable-tree-groups-embed-in-decidable-fg-self-similar-groups]], `H`
   embeds in a finitely generated self-similar group `S` with solvable word
   problem.
2. **The Higman step.** By
   [[decidable-fg-self-similar-groups-embed-in-fp-self-similar]], `S` embeds in a
   finitely presented self-similar group `P`.
3. **Composition.** `H <= S <= P`.

## Each prerequisite is necessary and can fail independently

- **Both halves are necessary.** The necessity sections of the two prerequisites
  show that each is implied by the target. So this route is an equivalence: the
  target holds iff both halves hold.
- **The halves concern different things.**
  - The first half is about section tables and the co-r.e. side.
    [[computable-tree-involution-escapes-local-self-similar-hulls]] already kills
    its uniform versions.
  - The second half is about relations and the r.e. side. Its inputs come with a
    table, and only finite presentation is missing.
  - A counterexample to the second half says nothing about hulls. The first half
    can fail on groups that are not self-similar, which the second half never
    sees.
- **Credit on the flagship route.** Through
  [[fp-rf-self-similar-embedding-via-computable-tree-actions]], the flagship
  [[every-fp-rf-group-embeds-in-fp-self-similar-group]] now needs three things:
  - [[every-fp-rf-group-acts-on-a-regular-rooted-tree]];
  - a non-uniform hull theorem;
  - a self-similar Higman theorem for inputs that come with a finite section
    table.
