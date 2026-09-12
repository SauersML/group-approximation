---
rg: 2
id: nested-idempotents-from-p-regular-intersections-are-equal
kind: claim
title: Nested equal-trace idempotents from two finite subgroups with p-regular intersection coincide
distinct_from:
  nested-two-finite-subgroup-idempotents-have-strict-rank: that proves a strict rank gap for properly nested idempotents from any two finite subgroups over any field, with no condition on the intersection; this is its special case k = F_p with p not dividing the order of the intersection, proved differently through a semisimple idempotent of the intersection.
  mixed-finite-subgroup-defects-need-infinite-generation: that excludes difference defects when the two finite subgroups generate a finite group, with no condition on their intersection; this allows an infinite join, assumes instead that the intersection has order prime to p, and concludes e = f outright.
  lifted-trace-detects-finite-subgroup-projectives: that separates nested idempotents inside ONE finite group algebra; this compares idempotents from two different finite subgroups, where e - f lies in no finite group algebra and the trace formula does not apply to it directly.
  leavitt-nested-idempotent-corner-module-equivalence: that asks whether one explicit trace-balanced nested pair over the torsion-free group Q is equivalent; this is a general coincidence theorem for idempotents supported in finite subgroups of any group.
artifacts:
  - research/artifacts/binary-kernel-nested-idempotents-2026-09-12.md
---

**ESTABLISHED** (route `nested-idempotents-p-regular-intersection-proof`; verified by
`w3-vf-linear`, Section 12.1). It is a special case of the earlier
`nested-two-finite-subgroup-idempotents-have-strict-rank` (established 2026-09-07), which needs no
condition on the intersection.

Let `p` be prime, `G` any group, and `H_1, H_2 <= G` finite subgroups whose intersection
`C = H_1 ∩ H_2` has order prime to `p`. Let `e in M_n(F_p[H_1])` and `f in M_n(F_p[H_2])` be
idempotents with `f <= e` (`ef = fe = f`), and suppose `t_p([e]) = t_p([f])` for the lifted
trace of `lifted-trace-detects-finite-subgroup-projectives`. Then `e = f`.

Consequences:
- **No mixed defect.** No pair `BA = I` has a nonzero defect `I - AB = e - f` with `e`, `f` as
  above: a defect has lifted trace `0`, which forces `t_p(e) = t_p(f)`, hence `e = f` and the
  defect is `0`.
- **No proper equivalence.** `f ~ e` in `M_n(F_p[G])` forces `e = f`.
- **The join may be infinite.** `H_1` and `H_2` need not lie in a common finite subgroup.
- **Binary candidates killed.** Over `F_2` this kills every candidate built from two finite
  subgroups meeting in an odd-order group, at any prefix levels. That includes subgroups
  meeting trivially and all idempotents from order-3, order-5 and order-7 cyclic constants.
  Even intersections are excluded too, by `nested-two-finite-subgroup-idempotents-have-strict-rank`,
  which refutes `modular-nested-idempotents-equivalent-over-leavitt-units`.

Proof: Sections 1–2 of the artifact.
