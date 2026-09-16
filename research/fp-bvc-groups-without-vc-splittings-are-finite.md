---
rg: 2
id: fp-bvc-groups-without-vc-splittings-are-finite
kind: claim
title: A finitely presented group with BVC and no splitting over a virtually cyclic subgroup is finite
distinct_from:
  finitely-presented-bvc-groups-are-virtually-cyclic: that is the full von Puttkamer–Wu conjecture; this adds the hypothesis that the group has no one-edge splitting over a virtually cyclic subgroup, and is equivalent to it only through bvc-groups-splitting-over-vc-subgroups-are-vc
  bvc-groups-splitting-over-vc-subgroups-are-vc: that settles the groups that do split over a virtually cyclic subgroup; this is the complementary case
---

**Statement.** Let `G` be finitely presented with property BVC. Suppose `G` is not
`A *_C B` with `C != A`, `C != B` and `C` virtually cyclic, and is not an HNN extension of a
subgroup along an isomorphism between virtually cyclic subgroups. Then `G` is finite.

**Equivalent form.** "Then `G` is virtually cyclic" says the same thing. An infinite virtually
cyclic group `V` has a finite normal `F` with `V/F` isomorphic to `Z` or `D_∞`
(`research/artifacts/bvc-vc-splittings-2026-09-16.md`, §0, (V4)). So `V = F ⋊ Z` is an HNN
extension over `F`, or `V = A *_F B` with `[A:F] = [B:F] = 2`. Either way `V` splits over a
finite subgroup.

Together with `bvc-groups-splitting-over-vc-subgroups-are-vc`, this claim is equivalent to
`finitely-presented-bvc-groups-are-virtually-cyclic` (route
`fp-bvc-vc-via-excluding-vc-splittings`).

## Attempts

- 2026-09-16 (swarm lane, reduction only). This case was isolated by proving
  `bvc-groups-splitting-over-vc-subgroups-are-vc`. What is known in this case:
  - No nontrivial splitting over a finite subgroup, so an infinite such `G` is one-ended, by
    Stallings' theorem (quoted from memory, not re-verified).
  - Positive first Betti number: if `G` maps onto `Z`, it is an ascending HNN extension of an
    infinite finitely generated `H` (`fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension`).
    Such a `G` splits over `H`, so `H` is not virtually cyclic. The hypothesis here does not
    exclude that shape. Groups with infinite abelianization are in scope only when `H` is not
    virtually cyclic.
- Where the counting method dies. The proof of `bvc-groups-splitting-over-vc-subgroups-are-vc`
  kills a normal infinite cyclic subgroup of the edge group to reach an amalgam of finite groups.
  For a non-virtually-cyclic edge group `C` two things fail:
  - `C ∩ aCa^{-1}` can be infinite of infinite index in `C`, so 2-transitivity does not give
    `[A:C]` finite;
  - there is no normal subgroup to kill with finite quotient factors.
  Osin's two-class groups times `Z` (`osin-group-times-z-has-bvc`) split as ascending HNN
  extensions over non-virtually-cyclic bases and have BVC. So no argument about splittings alone
  can remove finite presentation.
- Not tried: JSJ theory over virtually cyclic subgroups (Rips–Sela, Dunwoody–Sageev, Fujiwara–
  Papasoglu). It describes splittings a one-ended finitely presented group has, but says nothing
  about groups with none, which is the case here.
