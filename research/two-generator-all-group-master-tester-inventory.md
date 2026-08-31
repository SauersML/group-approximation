---
rg: 2
id: two-generator-all-group-master-tester-inventory
kind: route
title: Identify every all-group tester with the same universal host
target: two-generator-fp-all-group-master-tester
requires:
  - whitehead-universal-finitely-presented-container
  - two-generator-frattini-universal-containers
  - universal-all-group-subgroup-colimit-class-tester
  - universal-local-approximation-fixed-two-generator-test-group
  - classical-bass-fixed-two-generator-testers
  - luck-determinant-fixed-two-generator-tester
  - gottschalk-surjunctivity-fixed-two-generator-tester
  - kaplansky-direct-stable-finiteness-one-universal-group
---

Choose `U` to be the all-group host constructed in
[[whitehead-universal-finitely-presented-container]]. The route
[[two-generator-frattini-universal-containers-proof]] strengthens the
embeddings into this same host; it does not replace `U`.

Each required theorem makes an explicit compatible choice:

- the abstract subgroup-and-colimit theorem chooses this `U`;
- the local-approximation proof chooses this `U`;
- the all-group half of the classical Bass theorem uses the Frattini
  strengthening of this `U`;
- the determinant and Gottschalk testers apply the abstract theorem to
  this `U`; and
- the direct/stable-finiteness proof chooses this `U`.

Therefore all displayed equivalences hold simultaneously for one group.
The torsion-order calculation is inherited from the universal-container
construction. QED
