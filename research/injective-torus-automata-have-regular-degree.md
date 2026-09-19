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
- 2026-09-18 (swarm-0917-w11-w11-gs-follow) [group-rings]: C2 holds whenever `<supp D>` is
  residually-(locally indicable amenable) (RLA), at every `d`
  (`residually-li-amenable-groups-are-torus-surjunctive`, ESTABLISHED, unreviewed; artifact
  `research/artifacts/residually-li-amenable-torus-2026-09-18.md`).
  - **Criterion (Theorem 1).** Suppose `Q[H]` embeds in a division ring `E` inverting every
    matrix whose augmentation is invertible. Call this (AD_E). Then the constants
    `epsilon(D) in GL_d(Z)` already force `D` regular. No dynamics is used beyond the
    periodic-point lemma at `N = G`.
  - **Hosts.** Jaikin-Zapirain (Selecta 2021, imported as
    `residually-li-amenable-hughes-free-rings-are-universal`) proves `D_{Q[H]}` Cohn-universal
    for RLA `H`. A specialization to `epsilon` plus Gaussian elimination gives (AD_E).
    Free-by-(LI amenable) groups are RLA, so every `BS(m,n)` is.
  - **Belief change.** The w10 first open instance, `d = 2` over `BS(2,3)`, is closed at every
    `d`. `BS(2,3)` is finitely presented, non-Hopfian, not LEF and not amenable.
  - **Decomposition for torsion-free hosts.** C2 on a locally indicable `H` follows from (AD):
    Cohn specialization `D_{Q[H]} ~> Q` along `epsilon`, equivalently
    `rk_epsilon <= rk_{D_{Q[H]}}` on all matrices. (AD) is a pure ring statement, independent
    of soficity. It is open beyond RLA, since universality of `D_{Q[G]}` is published only for
    RLA and a few other classes. Thompson's `F`: every proper quotient is abelian, so `F` is
    RLA iff amenable. Hence `F` amenable implies C2 over `F`.
  - **Where it dies.**
    - (AD_E) forces `H` torsion-free: `N_K` for a finite `K` has `epsilon = |K|` and is a
      zero divisor. So hosts with torsion (non-LEF, non-RPP) are untouched.
    - RLA groups are sofic, so this adds nothing to Gottschalk itself, only to the torus lane.
  - **Import concern (flagged, not edited).**
    `flat-weak-bass-holds-exactly-for-locally-indicable-groups` item 1(ii) cites JZ21
    universality for every locally indicable `G`. The JZ21 abstract claims it only for RLA
    groups, so the dependent items are supported only on that class.
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
- 2026-09-19 (swarm-0917-w14-w14-gs-pull): kernel descent
  (`torus-degree-regularity-lifts-through-li-kernels`, ESTABLISHED; artifact
  `research/artifacts/torus-degree-li-kernel-descent-2026-09-19.md`).
  - **Mechanism.** For any normal `N` (infinite index allowed), `tau_N` on
    `Fix(N) = (T^d)^(G/N)` is injective of degree `p_N(D)`.
  - **Descent.** If `N` is locally indicable, regularity of `p_N(D)` lifts to `D`: apply
    Strebel's `D(Z) = LI` to the coset-block maps. It also lifts through locally normal
    `p` kernels (nilpotent lifting mod `p`, as in w10), through finite nilpotent kernels,
    through f.g. residually finite-nilpotent kernels, and along finite series of these.
  - **Consequences.**
    - C2 is closed under LI-kernel extensions.
    - It holds over every LI-by-(residually finite) group, e.g. `BS(2,3) × A_5` and
      `F × A_5`, which no earlier node covers.
    - A counterexample descends at the same `d` to a group with no nontrivial LI normal
      subgroup.
  - **Where kernel descent dies.** At kernels containing a finite subgroup of
    non-prime-power order: the Bezout element has `p_N(D) = 1`. So `Alt_fin(N)`, simple
    and containing `A_5`, is out of reach of every descent argument.
