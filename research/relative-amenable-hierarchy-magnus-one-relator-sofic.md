---
rg: 2
id: relative-amenable-hierarchy-magnus-one-relator-sofic
kind: claim
title: A relative amenable hierarchy of the Magnus piece down to a Magnus subgroup makes a one-relator group sofic
distinct_from:
  amenable-envelope-magnus-piece-one-relator-sofic: that assumes an amenable envelope built by finitely many moves; this assumes only tree actions on the piece itself, which every finite envelope induces and which in turn give leveled envelopes.
  peelable-extreme-one-relator-groups-are-sofic: that is the syllable criterion; this is the geometric criterion both envelope theorems specialize.
artifacts:
  - research/artifacts/envelope-relative-hierarchy-characterization-2026-09-11.md
  - research/artifacts/amenable-envelope-magnus-piece-sofic-2026-09-11.md
---

ESTABLISHED (written proof). Let `G = <a,t | w>` be torsion-free with a
zero-exponent Magnus piece `B_0` and free Magnus subgroups `F_-, F_+`. Call a
finite chain `B_0 = V_k >= ... >= V_0 = F_-` a **relative amenable hierarchy**
if each `V_i` acts on a tree such that:
* edge stabilizers are amenable;
* `V_(i-1)` is the stabilizer of a vertex;
* vertex stabilizers outside that orbit are sofic.

**Theorem.** If `(B_0, F_-)` or `(B_0, F_+)` has a relative amenable hierarchy,
then `G` is sofic.

Moreover, finite envelope => hierarchy => leveled envelope. So this is the
weakest of the three positive hypotheses. If `B_0` is sofic, for instance under
induction on relator length, the side soficity condition is automatic.
