---
rg: 2
id: stably-finite-group-ring-with-non-mf-elementary-groups
kind: claim
title: The integral group ring of the Leavitt unit group is stably finite although its elementary groups are not MF from rank two
distinct_from:
  leavitt-group-algebra-not-stably-finite: that is the open demand that the group algebra over the binary field fail stable finiteness; this is the established fact that the integral group ring is stably finite, by the trace on the reduced group C-star algebra, and that its elementary groups are nevertheless non-MF.
  properly-infinite-corner-forces-non-mf-from-rank-two: that derives non-MF elementary groups from a properly infinite idempotent in the coefficient ring; this ring has none, being stably finite, and its elementary groups are non-MF because the coefficient group itself is.
  exact-stably-finite-non-mf-reduced-group-algebra: that is a C-star statement about the reduced group algebra of the sofic witness; this is a ring-and-group statement about the integral group ring of the Leavitt unit group and its elementary groups.
  binary-leavitt-all-ranks-full-mf-radical: that is the non-MF theorem for the Leavitt unit group itself, consumed here; this is the consequence for elementary groups over its group ring and the resulting refutation of the ring equivalence.
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  Let `H = L_(F_2)(1,2)^x` be the Leavitt unit group and
`R = Z[H]` its integral group ring.  Then

* `R` is a countable, finitely generated, unital, **stably finite** ring:
  `AB = I` in `M_m(R)` implies `BA = I` for every `m`;
* `EL_n(R)` is **not MF** for every `n >= 2`; indeed
  `h |-> diag(h, 1, .., 1)` embeds `H` into `EL_n(R)`.

**What it refutes.**  The proposed equivalence "`EL_n(R)` is MF if and
only if `R` is directly finite" fails in the direction "finite ring
implies MF group", and it fails even with stable finiteness in place of
direct finiteness.  What survives as a target is the one-way implication
"`EL_n(R)` MF implies `R` directly finite": established in positive
characteristic at `n >= 4` by
`finite-additive-order-one-sided-defects-are-mf-invisible`, open in
characteristic zero (`integral-jacobson-elementary-group-is-not-mf`).
This example does not touch that direction.

**Two independent sources of non-MF elementary groups.**  Over
`L_(F_2)(1,2)` the non-MF property comes from the ring's one-sided
inverse (a full complementary idempotent); over `Z[H]` it comes from the
coefficient *group*, and the ring has no one-sided inverse at all.  A
ring-theoretic criterion for MF elementary groups must therefore see the
unit group of the coefficient ring, not only its idempotents.

**Ingredients.**  `H` is not MF and simple
(`binary-leavitt-all-ranks-full-mf-radical`), hence perfect
(`leavitt-gl-equals-el-and-perfect-unit-group`); the identity
`diag([a,b],1) = [diag(a,a^-1), diag(b,1)]` with `diag(a,a^-1) in EL_2(R)`
for units `a, b`; MF passes to subgroups; and Kaplansky's theorem that
group rings in characteristic zero are stably finite, through the
faithful trace on `C*_r(H)`.

Derivation: `stably-finite-group-ring-with-non-mf-elementary-groups-proof`.
