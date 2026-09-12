---
rg: 2
id: fg-simple-groups-not-biorderable-proof
kind: route
title: A maximal convex subgroup gives an Archimedean quotient, which Hölder embeds in the reals
target: finitely-generated-simple-groups-are-not-biorderable
requires: []
artifacts:
  - research/artifacts/stable-formalizability-on-simple-hosts-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Artifact, Section 2, Theorem 4.
1. **Maximal convex subgroup.** Convex subgroups of an ordered group form a chain. For finitely
   generated `G`, the union `C` of the proper convex subgroups is proper.
2. **Normality.** Conjugates of `C` are proper convex subgroups, so they lie in `C`.
3. **Archimedean quotient.** `G/C` is bi-ordered. For `a > 1` in `G/C`, the elements bounded by powers
   of `a` form a convex subgroup whose preimage strictly contains `C`, so it is everything.
4. **Hölder** (imported at statement level). `G/C` embeds in `(R, +)` and is nontrivial, so `G` is not
   perfect.
5. **Abelian case.** `Z/p` has torsion, so it is not bi-orderable.

**Verification.** `w3-vf-positive` passed this route (Section 11.3 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`).
