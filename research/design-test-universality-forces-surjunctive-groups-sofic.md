---
rg: 2
id: design-test-universality-forces-surjunctive-groups-sofic
kind: claim
title: At normal Dirac points the design inequalities cut out exactly surjunctivity, so universality or gap compilers decide surjunctivity of groups
distinct_from:
  hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups: that shows strict designs on the atomic hull need non-surjunctive or non-UQS groups; this shows that any method certifying non-co-soficity by design inequalities, or compiling Aldous-Lyons gaps into strict designs, already decides surjunctivity of groups.
  co-sofic-free-group-irs-carry-no-strict-design: that proves the design inequalities on co-sofic IRS; this identifies the full set they cut out at normal Dirac points and shows it is not the co-sofic set unless surjunctive groups are sofic.
  perfect-zpc-irs-quantum-gap-game: that is one finite game with a perfect IRS value and a quantum gap; this concerns the family of design tests and obstructs uniform ways of making them strict.
artifacts:
  - research/artifacts/design-subgroup-tests-2026-09-17.md
---

**ESTABLISHED** by `design-test-universality-forces-surjunctive-groups-sofic-proof`.

**Definition.** Let `S_des` be the set of IRS of `F_r` satisfying `delta_D <= C_D eps_D` for every design `D`,
with the heretic constant `C_D`. It is closed and convex, and it contains every co-sofic IRS.

**Theorem.** For `N` normal in `F_r` and `G = F_r / N`:
- (a) `delta_N in S_des` iff `G` is surjunctive;
- (b) `delta_N` is co-sofic iff `G` is sofic.

**Corollaries.**
- *Universality.* If `S_des` equals the co-sofic set, then every finitely generated surjunctive group is sofic.
  Universality at normal Dirac points is equivalent to "surjunctive iff sofic".
- *Compilers.* Suppose a compiler turns every perfect-completeness gap into a design strict at the gap's IRS. A
  perfect-completeness gap is a clopen `F`, an IRS `mu` with `mu(F) = 0`, and `inf` over finite Schreier graphs
  of `mu_X(F)` positive. Then every finitely presented non-sofic group is non-surjunctive.

**Obstruction.**
- Killed: every approach to `some-free-group-irs-carries-a-strict-design` that works uniformly at normal Dirac
  points, whether by universality or by compiling gaps. Each such approach refutes the goal as soon as a finitely
  presented non-sofic group exists.
- The invariant is the value pair `(eps, delta) in {0,1}^2` at normal Dirac points.
- Surviving approaches must use nonatomic IRS with `0 < delta_D < 1`.
