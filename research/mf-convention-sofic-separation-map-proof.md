---
rg: 2
id: mf-convention-sofic-separation-map-proof
kind: route
title: Assemble the convention-by-convention separation map
target: mf-convention-sofic-separation-map
requires: [weak-mf-does-not-imply-sofic, pure-mf-conventions-imply-sofic, maximal-group-cstar-infinite-under-strict-compression, reduced-mf-finite-amenable-radical-is-hyperlinear, reduced-mf-nonsofic-group-dichotomy]
---

Each row of the target's table is one prerequisite:

1. `weak-mf-does-not-imply-sofic` is the operator-MF row.
2. `pure-mf-conventions-imply-sofic` is the representation-field row.
3. `maximal-group-cstar-infinite-under-strict-compression` gives the full
   group C-star row.  The strict-compressor observation in the target body
   covers every nontrivial instance of the two nonsoficity criteria: an
   infranormal subgroup normalized by all its compressors is normal, and a
   nonstrict `t_1` makes `J` trivial.  An infinite full algebra is not stably
   finite, so it has no MF embedding.
4. `reduced-mf-finite-amenable-radical-is-hyperlinear` and
   `reduced-mf-nonsofic-group-dichotomy` give the reduced row.
5. The trace-regular row is immediate from the definition: operator-norm
   models whose normalized traces converge to the regular character have
   `tr -> 0` off the identity.  Every nontrivial element is then tracially
   visible, and `hyperlinear-elementwise-visibility` concludes.  This row is
   recorded in prose only and adds no prerequisite beyond those listed.
