---
rg: 2
id: free-group-irs-lie-in-the-atomic-irs-hull
kind: claim
title: Every invariant random subgroup of a free group is a weak-* limit of mixtures of atomic invariant random subgroups
distinct_from:
  non-cohyperlinear-irs-exists: that produces an IRS whose character is not an amenable trace; this asks whether every IRS is approximable by mixtures of finite conjugacy orbits, which by the hardness remark would make some atomic IRS non-co-hyperlinear.
  atomic-noncohyperlinear-irs-forces-nonhyperlinear: that converts an atomic non-co-hyperlinear IRS into a group; this is an approximation statement about the convex geometry of IRS space, with no trace hypothesis.
  co-sofic-irs-carry-no-strict-design: co-sofic IRS are the closed convex hull of finite-index atomic IRS; this allows atoms with infinite deck groups, such as Dirac masses at arbitrary normal subgroups.
artifacts:
  - research/artifacts/atomic-hull-uqs-transfer-2026-09-17.md
---

**OPEN.** For every `m >= 1`, every IRS of `F_m` lies in the weak-* closed convex hull of the ergodic IRS
of `F_m` that have an atom. Equivalently, it lies in the closed convex hull of the uniform measures on
finite conjugacy orbits of subgroups.

**Why it matters.** With `hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups` and
`surjunctive-groups-are-uniformly-quantitatively-surjunctive`, it gives the transfer step
`irs-strict-designs-yield-nonsurjunctive-groups` (route
`irs-strict-designs-yield-nonsurjunctive-groups-via-atomic-hull`).

**Hardness (conditional remark, artifact Section 4).** For `m >= 2` this claim implies that a
non-hyperlinear group exists.

- IRS characters are continuous and affine in `mu`.
- Amenable traces on `C*(F_m)` form a weak-* closed convex set. This is a standard fact, imported and not
  re-derived.
- So the ergodic non-co-hyperlinear IRS of `non-cohyperlinear-irs-exists` would force some ergodic atomic
  IRS to be non-co-hyperlinear.
- `atomic-noncohyperlinear-irs-forces-nonhyperlinear` then produces a non-hyperlinear group.

**Test cases.** The Bowen-Chapman-Lubotzky-Vidick non-co-sofic IRS and Manzoor's non-co-hyperlinear IRS.
By the hardness remark, placing the latter in the hull is itself a non-hyperlinear group construction.

## Attempts

- **Periodization of random Schreier graphs (w5-gs-heretic, 2026-09-17).** Deferred, and not a proof.
  - *Reformulation.* The rooted Schreier graph of an ergodic atomic IRS has a label-preserving
    automorphism group acting freely with finitely many orbits: the deck group `Q` acting on `Q x {1..k}`.
    So the claim asks that `mu`-random rooted Schreier graphs be weak limits of mixtures of cocompactly
    periodic Schreier graphs, with the root uniform over the finitely many orbits.
  - *The obvious attack.* Glue the `R`-balls of `mu` into a periodic graph whose deck group is built from
    the gluing.
  - *Where it dies.* Finite quotients reach only co-sofic IRS, and the Bowen-Chapman-Lubotzky-Vidick IRS
    is not co-sofic. An infinite deck group needs a group whose Schreier quotient reproduces the ball
    statistics, and no construction of one is known. By the hardness remark, for the Manzoor IRS such a
    group would already be non-hyperlinear.
