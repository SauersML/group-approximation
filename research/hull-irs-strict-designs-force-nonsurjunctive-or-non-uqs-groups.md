---
rg: 2
id: hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups
kind: claim
title: A strict design on an IRS in the closed convex hull of atomic IRS forces a group that is non-surjunctive or not uniformly quantitatively surjunctive
distinct_from:
  atomic-irs-strict-designs-are-nonsurjunctive-quotients: that is the exact case, one atomic IRS with eps = 0 giving a strict pair over its deck group; this allows weak-* limits of mixtures, where each atomic component has positive forward error and only a uniform deficit converts it into a contradiction.
  irs-strict-designs-yield-nonsurjunctive-groups: that asks for a non-surjunctive group from a strict design on every IRS; this handles only IRS in the atomic hull and allows the weaker conclusion that some surjunctive group is not UQS.
  co-sofic-irs-carry-no-strict-design: that counts image patterns on finite Schreier graphs; this runs over infinite deck groups through the UQS deficit and needs no finite model.
  amenable-extensions-of-uqs-groups-are-surjunctive: that transplants a strict pair from an extension to its kernel along Følner sets; this transplants almost-strict designs from layered coset spaces to their deck groups, recording the forward-bad layers as a full track.
artifacts:
  - research/artifacts/atomic-hull-uqs-transfer-2026-09-17.md
---

**ESTABLISHED** by `hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-proof`.

Let `Hull(F_m)` be the weak-* closed convex hull of the ergodic IRS of `F_m` that have an atom. If some
`mu in Hull(F_m)` carries a strict design (Section 2 of `irs-surjunctivity-heretic-2026-09-17.md`), then
some countable group is not surjunctive, or some countable surjunctive group is not uniformly
quantitatively surjunctive (UQS, as defined in `amenable-extensions-of-uqs-groups-are-surjunctive`).

**Quantitative core (Proposition 3.1 of the artifact).** Let `nu` be ergodic atomic with deck group
`Q = N(H)/H`, and suppose `Q` is UQS with constant function `delta_Q`. Let `D` be a design with alphabet
`A` and radii `R_tau`, `R_sigma`, and put `rho = R_tau + R_sigma`. Let `d_k` be the ball size in the
`2m`-regular tree. Then

```text
delta_D(nu) <= ( d_(R_tau) + d_(2 rho) ln|A| / delta_Q(A^(d_rho), d_rho) ) eps_D(nu).
```

**Named invariant.** The inequality holds with one constant on every family of atomic IRS whose deck
groups share a UQS constant function, and it passes to the closed convex hull of that family. A strict
design on a hull IRS must break this uniformity along its approximating deck groups. Embedding all deck
groups in one free product shows that this is possible only if that group is non-surjunctive or non-UQS.

- **Scope.** The hull contains every Dirac mass at a normal subgroup and every co-sofic IRS. It is not
  known whether it contains every IRS (`free-group-irs-lie-in-the-atomic-irs-hull`).
