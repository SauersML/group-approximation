---
rg: 2
id: rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group
kind: claim
title: UN middle rung — some finitely generated infinite simple algebra over a finite field has a unital rank model while some Kazhdan elementary group over it is not LEF
distinct_from:
  group-ring-lef-iff-group-lef-iff-elementary-group-lef: that realises the middle rung with the non-simple group algebra of a finitely generated amenable non-LEF group; this asks for a simple coefficient algebra, where uniform simplicity makes the elementary group simple modulo centre.
  fp-simple-algebra-over-finite-field-with-rank-model: that asks only for the ring; this asks for the Kazhdan non-LEF elementary group and follows from that ring plus the LEF converse.
---

**ESTABLISHED (unreviewed)** by the complete route `rank-modelled-non-lef-el-via-lef-converse`, repaired 2026-09-13 by lane
sk-subgroups.
- The earlier route `rank-modelled-non-lef-el-via-amenable-non-rf-subflow` (lane `un-sofic-not-lef`, 9ef8948121) is invalidated by
  `whitehead-diagonal-map-is-not-multiplicative`. It embedded `Γ_p` in `EL_N(R)` through a diagonal map that is not a
  homomorphism.

The ring is `R = LC(X, F_q) ⋊ Γ_p`, where `X` is a free minimal subflow of the finitely presented, amenable,
non-residually-finite Abels–Prüfer group `Γ_p`:
- it has Følner rank models;
- a LEF `EL_N(R)` with `N >= 4` would make the countable simple ring `R` exactly matricial, and then `R^× ⊇ Γ_p` would be LEF.

So `EL_4(R)` is not LEF.

The group-level strengthening, simple modulo centre and `F_q`-linear sofic, is
`simple-kazhdan-linear-sofic-non-lef-group-exists`. No finite presentation of the ring is used; the original
fp-ring route below stays conditional.

There are:
- a finite field `k`;
- a finitely generated, infinite, simple unital `k`-algebra `R` with a unital rank model over `k`;
- some `N >= 3`

such that `EL_N(R)` is Kazhdan and not LEF.

**Why it is the middle.**
- It sits strictly between the two calibrated ends of `kazhdan-elementary-approximation-type-mirrors-ring-type`:
  - the ring has a rank model, so it is stably finite and far from the paradox end;
  - but it is not exactly matricial, so it is not the Pestov end.
- **Payoffs.**
  - With centre `k`, `S_N` is `k`-linear sofic (`rank-modelled-simple-rings-give-linear-sofic-projective-el`).
  - Together with the open (M⇐) (`stably-finite-simple-rings-have-mf-elementary-groups`), it would give a
    finitely generated Kazhdan group of a simple ring that is MF but not LEF.

**Candidates.**
- The conditional route `non-lef-kazhdan-el-group-from-fp-rank-modelled-simple-algebra`, from a finitely
  presented simple rank-modelled algebra.
- Free minimal `Z^2` SFTs without covariant quantum tilings at every scale. They carry invariant measures and
  rank models, but they are not matricial (`matricial-z2-sft-crossed-products-give-quantum-tilings`,
  `free-minimal-z2-sft-is-quantum-rigid`). Labbé's `LC(Ω_U, F_q) ⋊ Z^2` is the concrete test case (un-calibration).
- **Rank 3 over this ring is open.** The LEF converse needs `N >= 4`.

**Review (un-verify-3, 2026-09-13): PASS of the earlier route.** Its non-LEF step, "the Whitehead embedding of the non-RF finitely presented `Γ_p`", used the non-multiplicative diagonal map and is superseded. The repaired route is queued with sk-verify-3. The second route requires the open `fp-simple-algebra-over-finite-field-with-rank-model` and cannot fire. `research/artifacts/un-review3-2026-09-13-part4.md` §8.
