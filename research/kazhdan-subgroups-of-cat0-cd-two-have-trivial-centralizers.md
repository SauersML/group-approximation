---
rg: 2
id: kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers
kind: claim
title: Infinite Kazhdan subgroups of a torsion-free cocompact CAT(0) group of dimension two have trivial centralizers, so rigid compression defects vanish there
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that kills rigid defects in sofic ambient groups through Kun--Thom normalization; this kills them in the Titz--Witzel kernels for a geometric reason, with no approximation hypothesis.
  hyperbolic-compression-centralizer-rigidity: that shows compressors normalize the finite centralizer of a non-elementary subgroup of a hyperbolic group; this proves the centralizer of an infinite Kazhdan subgroup is trivial in a torsion-free cocompact CAT(0) group of dimension two, which is not hyperbolic when it has flats.
  vcd-two-groups-contain-no-kazhdan-commuting-pairs: that makes a commuting partner meeting an infinite Kazhdan subgroup trivially finite; this adds the case where the partner has a power inside the subgroup, which needs the CAT(0) translation character.
---

**ESTABLISHED (unreviewed).** Let `K` be torsion-free with `cd K <= 2`, acting properly and
cocompactly by isometries on a CAT(0) space `X`. Let `Gamma <= K` be an infinite Kazhdan subgroup.
Then `C_K(Gamma) = 1`.

## Consequences

- **Rigid defects vanish.** For every pair `Gamma <= G <= H <= K` as in
  `sofic-groups-kill-rigid-compression-defects`, `C_H(Gamma) = 1`, so the rigid compression defect
  `[g z g^-1, gamma]` is trivial. A nontrivial rigid defect cannot certify nonsoficity of any
  subgroup of `K`.
- **Every recorded certificate is vacuous in the Titz Mite--Witzel kernels.** Each of them
  (`titz-witzel-simple-kazhdan-cat0-lattices-exist`) acts freely and cocompactly on a CAT(0)
  building of dimension two. Together with the other fences, no subgroup of such a kernel carries:
  - an instance of the expander-matching criterion
    (`vcd-two-groups-contain-no-kazhdan-commuting-pairs`,
    `kazhdan-compression-instances-have-infinite-vcd`);
  - a generalized wreath product with infinite lamps (same nodes);
  - a Kun--Thom double (`compressed-doubles-raise-cohomological-dimension`);
  - a nontrivial rigid compression defect (this node).
- **Pairs still occur.** Infranormal non-normal Kazhdan pairs are not excluded by dimension two in
  general (`cd-two-group-with-infranormal-kazhdan-pair`). Whether a Titz--Witzel kernel contains
  one is not decided. It would carry none of the certificates above.

Proof: `kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers-proof`.
