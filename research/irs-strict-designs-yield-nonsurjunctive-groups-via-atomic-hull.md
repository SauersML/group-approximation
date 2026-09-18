---
rg: 2
id: irs-strict-designs-yield-nonsurjunctive-groups-via-atomic-hull
kind: route
title: Approximate the design-carrying IRS by atomic mixtures and pay the forward error with a uniform quantitative deficit
target: irs-strict-designs-yield-nonsurjunctive-groups
requires:
  - free-group-irs-lie-in-the-atomic-irs-hull
  - surjunctive-groups-are-uniformly-quantitatively-surjunctive
  - hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups
artifacts:
  - research/artifacts/atomic-hull-uqs-transfer-2026-09-17.md
---

By modus ponens (artifact Section 5).

1. Let an IRS `mu` of `F_m` carry a strict design. `free-group-irs-lie-in-the-atomic-irs-hull` puts `mu`
   in the atomic hull.
2. `hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups` gives a countable group that is not
   surjunctive, or that is surjunctive and not UQS.
3. `surjunctive-groups-are-uniformly-quantitatively-surjunctive` excludes the second case.

**Each prerequisite can fail on its own.**

- The hull claim is about the convex geometry of `IRS(F_m)`. It fails if some nonatomic IRS is far from
  atomic mixtures, whatever holds for groups.
- The UQS claim is about groups. It can fail on a nonsofic surjunctive group while the hull claim holds.
- The third prerequisite is proved.

**Bypasses the recorded dead ends.** Diracization and joins try to build one group from `mu` and move a
defining condition the wrong way. This route uses the deck groups already present in approximating atoms,
and records the forward error as a full track instead of repairing it.

**Cost.** For rank at least 2 the hull claim implies that a non-hyperlinear group exists (artifact
Section 4).
