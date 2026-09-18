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
  - research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md
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
- 2026-09-18 (swarm-0917-w13-w13-gs-last1): the locally indicable case and the Fox witness
  (artifact `research/artifacts/torus-degree-locally-indicable-and-fox-witness-2026-09-18.md`).
  - **Positive** (`locally-indicable-groups-are-torus-surjunctive`, ESTABLISHED).
    - *Proof.* If `<supp D>` is locally indicable, `epsilon(D) in GL_d(Z)` already forces
      regularity at every `d`, by Strebel's `D(Z)` property
      (`strebel-class-dz-is-locally-indicable`, imported via Cochran–Harvey).
    - *What else follows.* Then `tau` is a homeomorphism and `D(tau) in GL_d(Z[G])`.
    - *New hosts.* The new non-RF host is `BS(2,3)` at every `d`. This answers the first test
      of need 7c18e718.
    - *Corrects w9.* Augmentation-only proofs do not work "exactly on RPP support". They also
      work on locally indicable support.
  - **Obstruction** (`fox-witness-kills-augmentation-torus-degree-proofs`, ESTABLISHED).
    - *The witness.* On any group with a nontrivial f.g. perfect subgroup, `(P J)^*` has
      `epsilon = I` and the nonzero left kernel row `(x_i^{-1} - 1)`. Here `J` is a Fox Jacobian
      and `P epsilon(J) = I`.
    - *Where augmentation-only proofs now die.* A second class, which contains torsion-free
      groups. Higman's group carries an explicit `4 x 4` witness.
  - **Open region for C2.** Support groups that are neither RPP nor locally indicable (nor LEF
    or abelian, by w10 results on another branch).
    - Every torsion-free group in this region has a nontrivial f.g. subgroup with finite
      abelianization. Where that subgroup is perfect, the Fox witness applies.
    - **Sharpest test.** Construct, or rule out, an injective `tau` on `(T^4)^H`, `H` Higman's
      group, with `D(tau)` the Fox witness. It would refute TS at `H`. The periodic tori give
      nothing there, since `H` has no finite quotients. C2 stays OPEN.
