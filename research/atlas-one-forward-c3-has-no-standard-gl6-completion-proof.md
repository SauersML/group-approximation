---
rg: 2
id: atlas-one-forward-c3-has-no-standard-gl6-completion-proof
kind: route
title: Boolean inverse-pair exhaustion of the one-forward GL6 fiber
target: atlas-one-forward-c3-has-no-standard-gl6-completion
requires: []
artifacts:
  - experiments/atlas_a4_gl6_forward_instance.py
  - experiments/atlas_a4_gl6_forward_sat.py
  - research/artifacts/atlas-a4-one-forward-gl6-unsat.json
---

`atlas_a4_gl6_forward_instance.py` reconstructs the canonical fourteen-word
core, collision `19243`, and the fixed forward word `(A4-GL6-FWD)`.  The solver
declares 72 Boolean variables: the 36 entries of `R` and the 36 entries of a
putative inverse `S`.  It imposes both `RS=SR=I` over `F2`, so its models are
exactly the elements of `GL_6(F2)` with no missed singularity case.

Every matrix product is encoded entrywise as XOR of six ANDs.  The script then
substitutes `j_2(g)=R diag(g,I_2) S` into all fourteen cubes, the collision
word, and the forward cube.  Z3 4.15.3 returns `unsat`.  A second run adds the
disjunction that `R` move at least one of the eight named generators of the
rank-three `GL_3(2)`; it too returns `unsat`.  The unrestricted run is the
proof of the claim, while the escape run independently checks the intended
commutant question.

As a separate exact sanity check,
`atlas_a4_gl6_bordered_forward_search.py` exhausts all 2,048 one-coordinate
borders over each of the two certified GL5 frames.  Exactly 1,024 borders per
base are invertible and neither family contains a survivor.
