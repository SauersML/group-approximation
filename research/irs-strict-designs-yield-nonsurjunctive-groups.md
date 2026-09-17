---
rg: 2
id: irs-strict-designs-yield-nonsurjunctive-groups
kind: claim
title: If some invariant random subgroup of a free group carries a strict automaton design then some group is not surjunctive
distinct_from:
  diracization-gap-equals-nonhyperlinear-group: that is the normal-Dirac gap for Connes embeddability of IRS characters; this is the transfer step for strict automaton designs, where the defining conditions are local tables rather than traces.
  atomic-irs-strict-designs-are-nonsurjunctive-quotients: that proves the transfer for atomic IRS; this asks for it for every IRS, including nonatomic ones on infinitely generated subgroups.
  surjunctive-decoder-subgroups-force-surjectivity: that descends a strict pair over a group to a subgroup of that group; this must manufacture a group from a random coset space with no ambient group.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

**OPEN.** If an IRS of some `F_r` carries a strict design (artifact Section 2), then some group is not
surjunctive.

- By `atomic-irs-strict-designs-are-nonsurjunctive-quotients` it is equivalent to: a strict design on
  some IRS yields a strict design on some atomic IRS.
- It is also equivalent to "Gottschalk implies `free-group-irs-carry-no-strict-design`".
- It can fail on its own. A nonatomic non-co-sofic IRS might carry a strict design while every group is
  surjunctive.

## Attempts

- **Diracization by iid intersection (a-gs-heretic, 2026-09-17).** It dies.
  - `character-diracization-limit` sends an IRS to its normal core.
  - For word-rule designs, intersections shrink stabilizers and refine coset tables. Forward
    sufficiency passes only to coarser tables, so forward-good sites can be lost.
- **Joins of independent samples (a-gs-heretic, 2026-09-17).** It dies. Joins coarsen tables and keep
  forward-good sites. But reverse failure passes only to finer tables, so reverse-bad sites can be lost.
- **Shape-dependent rules.** Changing the subgroup changes the shapes and hence the rules. Neither
  condition is monotone, and there is no mechanism to preserve both.
- **Finitely generated support.** If an ergodic IRS is supported on finitely generated subgroups, it has
  an atom and the atomic theorem applies. So only nonatomic, infinitely generated witnesses need a
  transfer.
- **Atomic approximation with a uniform deficit (w5-gs-heretic, 2026-09-17).** Proves the transfer on the
  atomic hull, up to UQS. Artifact `research/artifacts/atomic-hull-uqs-transfer-2026-09-17.md`.
  - **Proved.** `hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups`: a strict design on an IRS
    in the closed convex hull of atomic IRS yields a countable group that is non-surjunctive, or surjunctive
    and not UQS.
  - **Mechanism.** On each approximating atom, the forward-bad layers are recorded as a full track, which
    gives an injective automaton over the deck group into proper subshift tracks. UQS bounds
    `delta_D <= C eps_D`, and a free product of all deck groups makes `C` uniform.
  - **New decomposition** (route `irs-strict-designs-yield-nonsurjunctive-groups-via-atomic-hull`). This
    claim follows from `free-group-irs-lie-in-the-atomic-irs-hull`,
    `surjunctive-groups-are-uniformly-quantitatively-surjunctive` and the proved lemma. The two open
    prerequisites can each fail on their own.
  - **Where it still dies.** A nonatomic IRS outside the hull carrying a strict design. Excluding all such
    IRS through the hull claim needs a non-hyperlinear group, because an ergodic non-co-hyperlinear IRS in
    the hull would force an atomic one (artifact Section 4).
