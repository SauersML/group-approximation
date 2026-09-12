---
rg: 2
id: no-magnus-hierarchy-one-relator-groups-sofic
kind: claim
title: Torsion-free two-generator one-relator groups whose Magnus pieces have no relative amenable hierarchy are sofic
distinct_from:
  no-magnus-envelope-one-relator-groups-sofic: that is the remainder after finite amenable envelopes; this is the remainder after relative amenable hierarchies, a weaker hypothesis, so this class is contained in that one.
  torsion-free-two-generator-one-relator-groups-sofic: that is the whole class; this is the rigid core left by every amenable-edge argument on the Magnus piece.
artifacts:
  - research/artifacts/envelope-relative-hierarchy-characterization-2026-09-11.md
  - research/artifacts/hnn-fold-free-coset-wreath-2026-09-11.md
---

OPEN. Let `G = <a,t | w>` be torsion-free. Suppose that for every zero-exponent
basis, neither `(B_0, F_-)` nor `(B_0, F_+)` has a relative amenable hierarchy.
Claim: `G` is sofic.

Such a `G` is rigid in the following exact sense. In every basis, every tree
action of the Magnus piece with amenable edge stabilizers and a free Magnus
subgroup elliptic fails at some level to descend to that subgroup.

## Attempts

1. **Amenable splittings.** *Exhausted by definition.* The characterization
   artifact shows that finite envelopes, hierarchies and leveled envelopes are
   nested, so no amenable-edge move sequence on the piece reaches this class.
2. **Coset fold.** *Reduces to separating quotients.* `G` is the Magnus HNN
   extension of `B_0` over `F_- -> F_+`.
   [[hnn-folds-into-free-coset-wreath]] makes `G` sofic once some sofic quotient
   with a sofic coset action separates finitely many syllables. That is the open
   input [[rigid-magnus-groups-have-sofic-separating-quotients]].
