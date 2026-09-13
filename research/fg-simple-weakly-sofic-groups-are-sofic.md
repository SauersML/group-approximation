---
rg: 2
id: fg-simple-weakly-sofic-groups-are-sofic
kind: claim
title: Every finitely generated simple weakly sofic group is sofic
refuted_by:
  - fg-simple-weakly-sofic-nonsofic-group-exists
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
  Direct products of finite simple groups add nothing either
  (`simple-group-relator-templates-over-finite-simple-groups`).
- **Calibration against the Gottschalk gate.** This claim implies that `R^x` is linear sofic over no
  field. So it would settle `non-linear-sofic-group` with the witness `R^x` and refute
  `binary-leavitt-unit-group-is-f2-linear-sofic`. Conversely, that gate would refute this claim
  (`rigidity-counterexample-from-leavitt-f2-linear-soficity`, into the negation
  `fg-simple-weakly-sofic-nonsofic-group-exists`). Proving this claim is at least as hard as exhibiting a
  non-linear-sofic group.
- **Permanence cannot build a counterexample.** Extensions put a simple subgroup inside the kernel
  (`binary-leavitt-unit-group-is-weakly-sofic`, first attempt), and directed unions reach a finitely
  generated simple group at a finite stage. Glebsky's theorem produces no simple groups.
- **Not covered: countable simple groups.** A directed union of weakly sofic groups is weakly sofic,
  and Higman--Neumann--Neumann towers of HNN extensions produce countable simple groups containing a
  given group. If weak soficity passed to HNN extensions over cyclic subgroups, a torsion-free weakly
  sofic nonsofic seed would give a countable simple weakly sofic nonsofic group. That group is not
  finitely generated, so it would not refute this claim, and neither permanence input is on record.
- **Deep wreath targets: settled for full towers (2026-09-13, lane `ex-weak-sofic-deep-wreath`, unreviewed).**
  Kind (b) above cannot use full towers of the following kinds as targets, with any lengths. Each bound
  holds for every finitely presented group without finite quotients, uniformly in depth:
  - **All towers of bounded degree.** The width is bounded over every iterated wreath product of
    transitive groups of degree `<= m` (`simple-nonsofic-relator-width-over-iterated-wreath-products`, route
    `deep-wreath-relator-width-from-commutator-width`). The inputs are the template theorem
    `relator-width-over-towers-of-bounded-commutator-width` and the elementary commutator width bound
    `transitive-wreath-towers-bounded-commutator-width`. Abelian and solvable layers are included.
  - **Nilpotent-by-(locally finite variety) groups.** The width is bounded over these, for example
    congruence towers over a bounded residue group (`relator-width-over-nilpotent-by-locally-finite-groups`).
  - **Symmetric tops (simple nonsofic `G`).** The width is bounded over `H wr Sym(n)` and `H wr Alt(n)`
    with `|H|` bounded (`simple-nonsofic-width-over-bounded-base-symmetric-wreath`).
- **Affine and congruence targets over special linear tops: settled (2026-09-13, lane
  `ex2-weak-sofic-affine-targets`, unreviewed).** For finitely presented `G`, kind (b) gains nothing from:
  - *Transitive abelian layers.* Over `F_q^n x| SL_n(q)`, and over any extension by an abelian normal
    subgroup on which the group is transitive, the width exceeds the quotient's width by at most a fixed
    amount (`relator-width-over-transitive-abelian-extensions`).
  - *Congruence groups.* Over `SL_n(R)` for finite chain rings `R`, such as `SL_n(Z/p^k)` and
    `SL_n(F_q[t]/t^k)` with `n`, `q` and `k` all unbounded, and over `R^n x| SL_n(R)`, the width is bounded
    iff `G` is not linear sofic over finite fields. For bounded `n` it is bounded with no hypothesis
    (`simple-group-width-over-congruence-targets`).

  So `p`-group kernels of unbounded class under large special linear tops give no room when their layers
  are natural or adjoint modules. Two devices do the work: two Singer tori cover the whole congruence
  kernel by successive approximation, and for near-scalar tuples the nilpotent template matches the big
  kernel block.
- **What a refutation would look like now.** A simple nonsofic group with relator width tending to
  infinity, carried by one of:
  - finite groups of unbounded chief length that are not full wreath products, such as the subgroup
    generated by the tuple, where conjugators are scarce. By the Kaloujnine--Krasner embedding every finite
    group whose composition factors have order `<= m` is a subgroup of a tower of degree `<= m`, so this is
    the real room, for example finite solvable groups with bounded primes;
  - towers of unbounded degree under non-symmetric tops, where relator tops with short cycles defeat
    bounded dipole placement;
  - bases under symmetric tops that are not towers mixing bounded levels with symmetric levels
    (`simple-nonsofic-width-over-towers-with-symmetric-levels` excludes those);
  - `p`-groups under large classical tops whose layers are neither natural nor adjoint modules (many copies
    of the natural module, `Lambda^2`, mixed layers), isometry tops over chain rings, and tops with a large
    abelian quotient. These are the "Not covered" list of `simple-group-width-over-congruence-targets`.
  No such construction is known.
