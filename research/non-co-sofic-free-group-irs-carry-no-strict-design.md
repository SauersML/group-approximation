---
rg: 2
id: non-co-sofic-free-group-irs-carry-no-strict-design
kind: claim
title: No non-co-sofic invariant random subgroup of a free group carries a strict automaton design
refuted_by:
  - some-free-group-irs-carries-a-strict-design
distinct_from:
  free-group-irs-carry-no-strict-design: that is the whole IRS statement; this is its only unproved part, the IRS outside the weak-* closure of finite Schreier graphs.
  non-cohyperlinear-irs-exists: that supplies a non-co-hyperlinear IRS through its character; this asks whether any IRS outside the co-sofic closure supports an injective non-surjective local pair.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
  - research/artifacts/design-subgroup-tests-2026-09-17.md
---

**OPEN.** If `mu` is an invariant random subgroup of `F_r` that is not a weak-* limit of IRS of finite
`F_r`-sets, then `mu` carries no strict design (artifact Section 2).

- **Hole of** `irs-surjunctivity-via-co-sofic-split`.
- **Negation.** By `co-sofic-irs-carry-no-strict-design`, the negation is exactly
  `some-free-group-irs-carries-a-strict-design`.
- **Terminal branches.** Atomic witnesses already decide the goal
  (`atomic-irs-strict-designs-are-nonsurjunctive-quotients`). Ergodic witnesses supported on finitely
  generated subgroups have atoms. So the live branch is nonatomic IRS supported a.s. on infinitely
  generated subgroups. That is the same branch left open for Connes embeddability by
  `ergodic-nonce-irs-fg-support-is-terminal`.

## Attempts

- **Finite models (a-gs-heretic, 2026-09-17).** Every finite computation produces a co-sofic IRS. So
  neither a proof nor a counterexample can be checked on finite Schreier graphs, and the counting
  argument of the co-sofic case has nothing to count.
- **Diracization (a-gs-heretic, 2026-09-17).** It dies. Pushing a candidate IRS to its normal core by iid
  intersection refines tables and can destroy forward sufficiency. Artifact Section 6.
- **Design subgroup tests (swarm-0917-w7-w7-gs-follow, 2026-09-17).** A reframing. It leaves this node OPEN.
  See `design-subgroup-tests-2026-09-17.md`.
  - *Equivalent forms.* P1 is equivalent to Gottschalk for p.m.p. free-group graphings with measurable tables
    (`irs-surjunctivity-iff-pmp-graphing-surjunctivity`). It is also equivalent to its robust form, by
    compactness: approximate witnesses with `eps -> 0` and `delta >= eta` suffice for the negation.
  - *Test form.* A witness for the negation is a perfect-completeness Aldous-Lyons gap of the design test
    `T_{D,p}`.
  - *Decomposition of the negation.* It holds iff DIV and R both hold. DIV: some IRS violates
    `delta <= C_D eps`. R: repair to approximate witnesses.
  - *Where it dies.* It dies at uniform methods.
    - Universality of the design inequalities, and compilers from gaps to strict designs, decide surjunctivity at
      normal Dirac points (`design-test-universality-forces-surjunctive-groups-sofic`). The invariant is
      `(eps, delta) in {0,1}^2` there.
    - So a proof of the negation must use nonatomic IRS with `0 < delta < 1`.
    - A proof of this node cannot come from the HOT tools unless they prove P1, since those tools hold verbatim on
      IRS networks (`hot-surjunctivity-tools-hold-on-irs-schreier-networks`).
  - *Open search target.* Non-sofic free actions of sofic groups carrying strict pairs with proper-subshift
    table processes. Full-support tables are excluded by artifact Proposition 1.2.
