---
rg: 2
id: simple-el-group-middle-regime-is-a-central-extension-effect
kind: claim
title: If EL_N(R) is simple modulo its centre, a middle MF rank needs MF to fail to lift through a central extension
distinct_from:
  mf-rigidity-is-monotone-in-matrix-rank: that defines the MF spectrum and proves monotonicity for every ring; this shows the middle regime at a rank where EL_N is simple modulo centre can only come from a nontrivial central kernel
  toeplitz-ring-has-infinite-middle-mf-regime: that exhibits an infinite middle regime over a non-simple ring, where EL_N has non-central proper normal subgroups; this shows such a middle regime cannot occur when EL_N is simple modulo a trivial centre
artifacts:
  - research/artifacts/un-m-converse-simple-spectrum-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `R` be a countable unital ring with `1 ≠ 0`, `N ≥ 2`, and `G = EL_N(R)`. Assume every
normal subgroup of `G` is central or all of `G`.
- (a) Every nontrivial homomorphism `φ: G → H` into an MF group has `K = ker φ ≤ Z(G)`, and `G/K` is MF.
- (b) If `Z(G) = 1`, then `G` is MF iff `G` has a nontrivial homomorphism to an MF group. So `N` is not in the middle
  regime of `R` (for `mf`, `rig` as in `mf-rigidity-is-monotone-in-matrix-rank`).
- (c) If `N` is in the middle regime, some `1 ≠ K ≤ Z(G)` has `G/K` MF while `G` is not MF: MF fails to lift through
  `1 → K → G → G/K → 1`.

Proof in the route (artifact §2). The statement is elementary and very likely folklore in substance. Its use here is
the collapse of the MF spectrum of simple rings: see `f2-steinberg-elementary-groups-have-no-middle-mf-regime`.

**Review (un-verify, 2026-09-13): PASS.** (a) a proper normal subgroup is central and the image is MF as a subgroup; (b) trivial centre makes a nontrivial MF map injective, and the identity witnesses the converse since `e_12(1) ≠ I`; (c) follows. Elementary and folklore in substance (for simple groups, MF iff a nontrivial MF quotient exists), as the node says. See `research/artifacts/un-review-2026-09-13-part11.md` §1.
