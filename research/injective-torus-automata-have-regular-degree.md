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
- 2026-09-17 (swarm-0917-w10-w10-gs-break) [host-geometry]: the Next test is answered
  negatively, and C2 holds over every abelian group. Artifact
  `research/artifacts/torus-normal-p-lifting-2026-09-17.md`.
  - **Restriction to infinite-index normal subgroups.** For every `N <| G`, `tau` restricts
    to an injective torus automaton on `Fix(N) = (T^d)^(G/N)` with degree `p_N(D)`. This is
    the periodic-point lemma without finite index, with no invariance of domain.
  - **Lifting** (`torus-surjunctivity-lifts-through-normal-p-subgroups`, ESTABLISHED).
    Suppose `N` is a locally normal `p`-subgroup and `tau_N` is onto. Then `p_N(D)` is a
    unit, `D mod p` is invertible (nilpotent kernel ideal of a finite normal `p`-subgroup),
    `D` is regular, and `tau` is onto.
  - **Abelian hosts** (`abelian-groups-are-torus-surjunctive`, ESTABLISHED). Peel off the
    primary components met by `supp D`, and finish on `Z^k` support with the RPP theorem.
    - For `D = s + s^2 - t`, the image mod the 2-part is `s + s^2 - 1`, of value `-2` at
      `s -> omega`, so it is not a unit.
    - So no injective `tau` on `T^(Q/Z)` or `T^(Z(2^inf) x Z(3^inf))` has this degree.
  - **Belief change.** "Smallest open host `Z(2^inf) x Z(3^inf)`" is false.
    - A counterexample descends to `G/N` for every locally normal `p`-subgroup `N` and
      every finite solvable normal subgroup.
    - So minimal hosts have none. New smallest candidate: `Alt_fin(N)`, which is simple,
      locally finite, amenable and not residually finite.
    - New test there: the Bezout witness `2 P_t - P_s` in a copy of `A_4`.
  - **Where it stops.** On a simple host, Lemma 1 sees only the constants. Fixed sets of
    non-normal finite `K` are `tau`-invariant, but they are not full shifts over a group,
    so no surjectivity can be imported there.
