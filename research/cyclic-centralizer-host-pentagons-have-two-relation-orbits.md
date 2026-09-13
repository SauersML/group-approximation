---
rg: 2
id: cyclic-centralizer-host-pentagons-have-two-relation-orbits
kind: claim
title: In a host with cyclic centralizers, a 5-cycle of a support-3 Kaplansky graph reads one of two relators up to automorphism
distinct_from:
  cyclic-centralizer-hosts-have-square-free-kaplansky-graphs: that excludes cycles of length at most four in the same hosts; this classifies the 5-cycles that are not excluded.
  abdollahi-taheri-pentagon-relations-73-and-77-are-trefoil-type: that corrects two rows of the published 5-cycle table; this is the full census of that table in hosts with cyclic centralizers.
artifacts:
  - research/artifacts/zds-three-support-theory-2026-09-13.md
---

**ESTABLISHED.** Let `G`, `k`, `alpha`, `beta` be as in
`cyclic-centralizer-hosts-have-square-free-kaplansky-graphs`, with
`supp alpha = {1, h_2, h_3}`. The 1026 tuples of a 5-cycle fall into 105
classes under rotation and reversal (A--T's count), and:
1. 15 classes force `<h_2, h_3>` cyclic and 18 force it solvable. These are
   impossible in every torsion-free host.
2. 30 classes force `u^a = v^b` for generators `u, v` with
   `(|a|, |b|) in {(3,2), (4,2), (3,3)}`, and 6 force
   `u v^2 u^-1 = v^(+-2)`. These are impossible when centralizers are cyclic.
3. In each of the remaining 36 classes, some automorphism of `F(h_2, h_3)`
   followed by a signed permutation of the letters carries the relator to a
   cyclic conjugate of `h_3^-2 h_2^-2 h_3 h_2` or of `h_3^-2 h_2^-1 h_3^-1 h_2^2`.

So in a host with cyclic centralizers every 5-cycle of the Kaplansky graph
reads, in suitable generators, one of the two relators in item 3. The census
does not decide whether either can occur. For 6-cycles the same census gives
351 classes (A--T's count): 18 cyclic, 40 solvable, 48 torus, 12
Baumslag--Solitar with both exponents at least 2, and 233 unrecognized. So
single-cycle relations stop being a useful exclusion tool at length 5.

DERIVATION
[[cyclic-centralizer-host-pentagon-census-proof]]
