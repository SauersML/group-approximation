---
rg: 2
id: injective-torus-automata-have-regular-degree
kind: claim
title: Over every group, an injective continuous equivariant self-map of a torus full shift has a degree matrix that is regular over Q[G]
distinct_from:
  torus-automata-over-rf-or-domain-groups-are-surjunctive: that proves this regularity in two cases, residually finite groups and the circle alphabet over domain group rings; this is the statement for every group and every torus dimension.
  gottschalk-surjunctivity-conjecture: the dead co-Hopfian lease on that node used homology of pattern permutation modules of finite shifts, where every automaton acts as the identity; here the alphabet is connected, first cohomology is the free module Z[G]^d, and automata act by a nontrivial degree matrix.
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

For every countable group `G`, every `d >= 1`, and every injective continuous
`G`-equivariant `tau: (T^d)^G -> (T^d)^G`, right multiplication by the degree matrix
`D(tau)` is injective on `Q[G]^d`.

Together with `torus-automata-with-regular-degree-are-surjective` this gives
`every-group-is-torus-surjunctive`. The statement is a topological invariance-of-domain
principle for `G`-full shifts over tori. It involves no finite alphabet, so it can fail
independently of Gottschalk's conjecture.

## Attempts

- 2026-09-17 (swarm-0917-w4-gs-decomp-new): artifact Section 3.1.
  - **Known cases.**
    - Residually finite `G`, all `d`.
    - `Q[G]` a domain, `d = 1`.
    - Both come from invariance of domain on periodic tori.
  - **Obstruction to the constants-only argument.**
    - *What the constants give.* Only `epsilon(D) in GL_d(Z)`.
    - *Why that is not enough.* In `Z[Z/2 x Z/3]`, `D = s + s^2 - t` has
      `epsilon(D) = 1` and kills `(1-t)(1-s)`. So over a non-residually-finite host with
      torsion, or with `d >= 2`, a proof must see beyond finite-dimensional invariant
      submanifolds.
    - *What would replace them.* An infinite-dimensional invariance of domain: a strict
      decrease of a mean-dimension-type invariant on proper subsystems. That is sofic
      mean dimension over sofic groups, and nothing is known beyond them.
  - **How a counterexample would look.** An injective torus automaton with a singular
    degree matrix. Every character `x -> <gxi, x>` with `xi D = 0` pulls back to a
    nullhomotopic function on the image. So the image is an equivariant copy of the full
    torus shift on which a whole `G`-module of characters is homotopically trivial.
- 2026-09-17 (swarm-0917-w9-w9-gs-break): the augmentation dichotomy
  (`torus-degree-regular-on-prime-power-residual-support`, ESTABLISHED; artifact
  `research/artifacts/torus-degree-prime-power-support-2026-09-17.md`).
  - **Positive.** C2 depends only on `H = <supp D>`, via a coset decomposition of `Q[G]^d`.
    If `H` is residually prime-power (RPP), then `epsilon(D) in GL_d(Z)` already forces
    regularity at every `d`. The proof uses the nilpotent augmentation ideal of `F_p[P]`
    in a `p`-group quotient injective on `supp v`. New hosts: `Q`, `Z(p^inf)`,
    `Q (+) Z(p^inf)`, and locally finite `p`-groups, all at every `d`.
  - **Where augmentation-only proofs die.** On any `H` with a finite subgroup of
    non-prime-power order, `a P_s + b P_t` with `ap + bq = 1` has `epsilon = 1` and is a
    zero divisor. The `Z/6` example above is the case `p, q = 2, 3`.
  - **Belief change.** The smallest open host is `Z(2^inf) x Z(3^inf)` (or `Q/Z`).
    - It is locally finite, amenable and divisible, and has no finite quotients.
    - Finite-alphabet Gottschalk over it is elementary.
    - So C2, and TS, are open where GOT is trivial. The heuristic "TS is the easy
      characteristic-zero shadow" behind `gottschalk-via-torus-alphabet-degree-transfer`
      fails.
  - **Next test.** Construct, or rule out, an injective `tau` on `T^(Q/Z)` with
    `D = s + s^2 - t`. On every finite-subgroup block it would have degree 0, so it must
    carry information between blocks with unbounded memory.
- 2026-09-18 (swarm-0917-w10-w10-gs-follow): C2 holds for every LEF group, at every `d`
  (`lef-groups-are-torus-surjunctive`, ESTABLISHED, unreviewed; artifact
  `research/artifacts/lef-torus-small-fibre-2026-09-18.md`).
  - **Key input.** A dimension-free small-fibre lemma: a map `T^N -> T^N` with fibres
    of sup-diameter `<= 1/16` is onto and bijective on `H^1`, with the constant
    independent of `N`.
  - **Finite models.** Uniform injectivity of `tau` makes the fibres of exact LEF-model
    maps `tau_Q` small, and `tau_Q^* = phi(D)`. So `phi(D) in GL_d(Z[Q])`, and `D` is a
    two-sided non-zero-divisor.
  - **Belief change: the w9 conclusion is refuted.** Locally finite groups are LEF, so
    C2 and TS hold on `Q/Z`, `Z(2^inf) x Z(3^inf)` and `Alt_fin(N)`, all previously
    listed as smallest open hosts. The w9 next test is answered negatively:
    `D = s + s^2 - t` never occurs for an injective `tau` over an LEF group.
  - **New host.** `FSym(Z) ⋊ Z` is finitely generated, LEF and not residually finite.
  - **What stays open.** Finitely presented LEF groups are residually finite, so the
    remaining open hosts are non-LEF. The first cases are `d = 2` over `BS(2,3)` or
    Thompson's `F`, since `d = 1` is covered there by the domain case. Non-LEF groups
    with torsion and nonsofic groups remain open too.
  - **Obstruction (artifact Section 5).** No defect-tolerant small-fibre lemma exists.
    - *Example.* A map `T^N -> T^N` can be injective in `N - 1` coordinates and still
      satisfy `f^* = 0`: embed `T^(N-1)` in a small ball.
    - *Consequence.* The sofic extension must use locality of `tau_sigma` at the
      defects, not only a fibre bound.
  - The node stays OPEN for general `G`.
