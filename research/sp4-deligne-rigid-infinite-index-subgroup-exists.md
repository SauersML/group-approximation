---
rg: 2
id: sp4-deligne-rigid-infinite-index-subgroup-exists
kind: claim
title: Some finitely generated infinite-index subgroup of Sp_4(Z) keeps Deligne's mod-three class virtually nonzero
distinct_from:
  deligne-flexible-subgroup-restrictions-carry-exact-sector-models: that proves flexibility, with exact sector models, for finite, amenable, virtually free, surface and free-by-free product subgroups; this asks whether any finitely generated infinite-index subgroup escapes flexibility.
  deligne-covers-of-sp2g-z-have-finite-residual-2z: that is Deligne's rigidity theorem for the whole group and hence for its finite-index subgroups; this asks for rigidity on an infinite-index subgroup.
---

**OPEN.** Let `alpha in H^2(Sp_4(Z);Z/3)` classify Deligne's triple cover `E_3`. The claim is that there is a finitely
generated `B <= Sp_4(Z)` with `[Sp_4(Z):B] = infinity` such that `alpha|_(B')` is nonzero in `H^2(B';Z/3)` for every
finite-index `B' <= B`. Equivalently, by
(F1) of `deligne-flexible-subgroup-restrictions-carry-exact-sector-models`, the preimage `B~` is not residually finite.

**Why it matters.**
- By (F4) of `deligne-flexible-subgroup-restrictions-carry-exact-sector-models`, a proof of
  `deligne-nontrivial-maslov-opnorm-sectors-are-empty` must use relations of `E_3` that generate a rigid subgroup.
- **If this claim fails,** every such proof must use relations generating a finite-index subgroup. Then no
  infinite-index localization of the gate exists.
- **If it holds for `B`,** operator-norm emptiness of the `omega`-sector of `B~` implies the gate, by restricting
  models. This gives a new target whose own prerequisites can each fail.

**Constraints on candidates.**
- Such a `B` is non-amenable, not virtually free, and not virtually a surface group or a product of two virtually
  free groups, and not contained in `SL_2(Z) x SL_2(Z)` or in a maximal parabolic (all flexible).

## Attempts
- **2026-09-18, swarm-0917-w6-w6-deligne-break: standard subgroups are all flexible, so the attack is deferred.**
  Every structured infinite-index subgroup checked is flexible: finite, amenable, virtually free, virtually surface,
  and subgroups of `SL_2(Z) x SL_2(Z)` or of a maximal parabolic. The natural next test is a Zariski-dense subgroup
  with `vcd >= 2` that is not a product, such as a free product with amalgamation of two parabolics along their
  intersection. Its cover need not be residually finite, but no computation of `alpha` on its `H_2` has been made.
  Note that free products of flexible groups are flexible, since virtual `H^2` of a free product is the direct sum
  of the factors' virtual `H^2`. So the amalgam is the first place where rigidity can appear.
- `B` is not normal: by Margulis, normal subgroups of `Sp_4(Z)` are finite or of finite index (recalled, not re-read).
- If `B` is good in Serre's sense at the prime 3, then `B` is flexible.
- Candidates are therefore Zariski-dense thin subgroups of cohomological dimension at least 2 that fail 3-goodness
  in degree 2.
