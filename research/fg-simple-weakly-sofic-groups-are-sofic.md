---
rg: 2
id: fg-simple-weakly-sofic-groups-are-sofic
kind: claim
title: Every finitely generated simple weakly sofic group is sofic
distinct_from:
  simple-group-relator-width-in-finite-simple-targets: that proves the width bound of a finitely presented simple nonsofic group over symmetric, alternating, sporadic and bounded-rank targets; this asks for the conclusion over all finite groups at once, for finitely generated simple groups.
  weakly-sofic-not-sofic: that separates the two classes with a non-simple group; this asks whether simple groups can separate them.
  non-weakly-sofic-group-exists: that is the existence of a non-weakly-sofic group; this rigidity statement implies it through a simple Kazhdan envelope of the Kun--Thom wreath.
---

**OPEN.** If `G` is a finitely generated simple group that is weakly sofic, then `G` is sofic.

**Payoff.** It implies `non-weakly-sofic-group-exists`
(`non-weakly-sofic-group-from-simple-weak-sofic-rigidity`). The Kazhdan case alone suffices, since
the Kun--Thom wreath embeds in a finitely generated simple Kazhdan group. For the binary Leavitt unit
group it would give non-weak-soficity outright. A single finitely generated simple weakly sofic
nonsofic group refutes it.

## Attempts

- **Every natural target collapses.** For a finitely presented
  simple nonsofic `G`:
  - weak models whose lengths are support functions of finite actions are sofic models;
  - weak models whose lengths are rank functions are linear sofic models
    (`simple-group-support-and-semisimple-rank-models-collapse`);
  - the relator width is bounded over symmetric, alternating, sporadic, bounded-rank Lie type and
    nilpotent groups (`simple-group-relator-width-in-finite-simple-targets`,
    `perfect-group-relator-width-over-nilpotent-groups`).
- **Finite simple targets: settled (2026-09-13, lane `ex-weak-sofic-classical-covering`, unreviewed).**
  A finitely presented simple group has bounded relator width over **all** finite simple groups iff it
  is not linear sofic over finite fields (`simple-group-width-over-all-finite-simple-groups`). The
  classical input is `simple-group-psl-width-is-finite-field-linear-soficity` and
  `simple-group-classical-width-finite-field-linear-soficity`. So for finitely presented `G`, a
  counterexample must be of one of two kinds:
  - (a) linear sofic over finite fields and nonsofic. That is a finite-field, simple-group answer to
    Arzhantseva--Paunescu Question 8.5 (`linear-sofic-nonsofic-group`), so it is at least as hard to
    find as a linear sofic nonsofic group.
  - (b) weakly sofic only through non-simple finite targets of unbounded chief length outside the good
    classes, such as deep iterated wreath products with non-nilpotent tops (lane
    `ex-weak-sofic-deep-wreath`).

  An earlier version of this bullet listed classical groups of unbounded rank as possible room. That
  room is exactly (a): classical targets contribute linear soficity over finite fields and nothing more.
- **Permanence cannot build a counterexample.** Extensions put a simple subgroup inside the kernel
  (`binary-leavitt-unit-group-is-weakly-sofic`, first attempt), and directed unions reach a finitely
  generated simple group at a finite stage. Glebsky's theorem produces no simple groups.
- **Not covered: countable simple groups.** A directed union of weakly sofic groups is weakly sofic,
  and Higman--Neumann--Neumann towers of HNN extensions produce countable simple groups containing a
  given group. If weak soficity passed to HNN extensions over cyclic subgroups, a torsion-free weakly
  sofic nonsofic seed would give a countable simple weakly sofic nonsofic group. That group is not
  finitely generated, so it would not refute this claim, and neither permanence input is on record.
- **What a refutation would look like.** Finite groups with many layers and thin conjugacy classes,
  such as iterated permutational wreath products with non-nilpotent tops, carrying Glebsky's capped
  conjugation word lengths, on which a simple nonsofic group has relator width tending to infinity.
  No such construction is known.
