---
rg: 2
id: weakly-sofic-groups-can-carry-rigid-defects
kind: claim
title: Weakly sofic groups can carry nontrivial rigid compression defects
distinct_from:
  weakly-sofic-not-sofic: that separates weak soficity from soficity; this records the mechanism-level reason, the failure of the rigid defect criterion in the weakly sofic class, and hence the failure of Kazhdan centralizer normalization in some metric ultraproduct of finite groups.
  sofic-groups-kill-rigid-compression-defects: that is the criterion holding in the sofic class; this is the same criterion failing one class up.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED.** The Kun--Thom coset wreath `W` over the Theorem E pair has
two properties:

- it is weakly sofic (`weakly-sofic-not-sofic`);
- it carries a nontrivial rigid compression defect
  (`kun-thom-wreath-carries-rigid-defect`).

So the criterion "approximable groups have trivial rigid defect" fails for
weakly sofic groups. By `rigid-compression-defect-normalization-dichotomy`,
some homomorphism of the pair into a metric ultraproduct of finite groups
with bi-invariant metrics fails to normalize the centralizer of `Gamma`.

**What the class lacks.** Finite groups with arbitrary bi-invariant metrics
have no Hilbert structure on which property (T) could round, and no faithful
conjugation-invariant size. Both ingredients of the sofic proof are missing;
see artifact Section 10.

Derivation: `weakly-sofic-groups-can-carry-rigid-defects-proof`.
