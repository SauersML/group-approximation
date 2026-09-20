---
rg: 2
id: hyperlinear-group-actions-have-ce-covariant-models
kind: claim
title: Every measure-preserving action of a countable hyperlinear group on a probability space has a covariant model in a Connes-embeddable tracial algebra
distinct_from:
  tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce: that assumes CE of every crossed product of the one group F2 x F2 and concludes hyperlinearity of lattices; this asks, for every hyperlinear group and every action, only for some CE covariant model, which may carry a trace different from the crossed-product trace.
  gkp-connes-embeddable-generalized-wreath-permanence: that is a permanence theorem for generalized wreath products over sofic actions; this is a permanence statement for covariant models of arbitrary non-free measure actions of hyperlinear groups.
  ce-relation-full-group-subgroups-are-hyperlinear: that passes from a CE relation factor to hyperlinear subgroups; this runs in the opposite direction, from a hyperlinear group to a CE model of its action.
  paunescu-sofic-action-class-permanence: that concerns soficity of actions for amenable and free groups and amalgams; this concerns Connes-embeddable covariant models for all hyperlinear groups.
---

**OPEN.** Prerequisite Q1 of `nonhyperlinear-via-full-subgroup-covariant-models`.

**Statement.** Let `Gamma` be a countable hyperlinear group and `Gamma -> Aut(X, mu)` a measure-preserving action on
the measure algebra of a standard probability space. Then there are a tracial von Neumann algebra `(M, tau)` that
embeds trace-preservingly in `R^U`, a homomorphism `pi : Gamma -> U(M)`, and a normal unital trace-preserving
`*`-homomorphism `e : L^infinity(X) -> M`, such that `pi(g) e(f) pi(g)^* = e(f o g^-1)` for all `g` and `f`.
Covariant models are defined in `support-covariant-models-carry-fixed-point-trace`.

**Reformulation.** Q1 for `(Gamma, X)` is equivalent to the existence of a tracial state on the algebraic crossed
product `L^infinity(X) ⋊_alg Gamma` that restricts to `integral . d mu` on `L^infinity(X)` and whose GNS von Neumann
algebra is CE. Normality of `e` is automatic. If `f_i` increases to `f`, then `e(f_i)` increases to some
`y <= e(f)` with `tau(y) = sup integral f_i = integral f = tau(e(f))`, and faithfulness of `tau` gives `y = e(f)`.

**How it can fail.** A counterexample is a hyperlinear `Gamma` with an action whose every covariant model is non-CE:
the crossed product `L^infinity(X) ⋊ Gamma` and every intermediate trace `f u_g -> integral_(S_g) f dmu`, for
equivariant fields of subgroups `S`, would all have to be non-CE. This is independent of Q2 of the route.

## Attempts

- **Amenable groups (holds).** `L^infinity(X) ⋊ Gamma` is injective when `Gamma` is amenable. By Connes it is
  hyperfinite, hence CE, and it is a covariant model.
- **Free groups (holds).** For `Gamma = F_m` and any action, `L^infinity(X) ⋊ F_m` is the amalgamated free product
  over `B = L^infinity(X)` of the `m` algebras `L^infinity(X) ⋊ Z`. Each is injective, hence CE, and `B` is abelian,
  hence hyperfinite. Brown--Dykema--Jung Corollary 4.5 (verbatim quote in
  `amenable-by-virtually-free-twisted-crossed-products-are-ce-proof`) applied `m-1` times gives a CE crossed product.
- **Sufficient condition.** Q1 follows from the stronger open statement "every crossed product of a pmp action of a
  hyperlinear group is CE". Q1 is logically weaker, because a CE model with a trace other than the crossed-product
  trace suffices. No example is known here where only such a model is CE.
- **Q1 equals the crossed-product statement; it decides the Kun--Thom wreath (swarm-0917, 2026-09-18).**
  In any covariant model of an essentially free action, covariance alone kills `tau(e(f) pi(g))` for
  `g != 1`, so the model contains `L^infinity(X) ⋊ Gamma`. Padding any action by the Bernoulli shift of
  `Gamma` makes it free and keeps the old crossed product as a subalgebra. So Q1, group by group, is
  equivalent to "every crossed product of `Gamma` is CE", by `free-action-covariant-models-contain-the-crossed-product`.
  The "Sufficient condition" entry above is therefore an equivalence, and the "How it can fail" list
  reduces to one condition: some crossed product is non-CE. At the residually finite Kun--Thom group `G`,
  Q1 makes the binary coset wreath `W` hyperlinear, hence a hyperlinear nonsofic group
  (`hyperlinear-nonsofic-via-ce-covariant-models`). Every route that proves `W` or the Kun--Thom double
  nonhyperlinear refutes Q1. The sofic analogue fails at this `G` (`kun-thom-free-nonsofic-action`).
  Q1 also implies `f2xf2-crossed-products-are-connes-embeddable`.
- **Q1 forces closure under solvable and finite kernels, and so excludes whole NH lanes
  (swarm-0917 w12, 2026-09-18).** See `ce-covariant-models-force-solvable-kernel-closure`.
  - Kaloujnine--Krasner puts every abelian-by-`Lambda` group inside `C ⋊ Lambda` for a countable
    abelian `C ≤ A^Lambda`, and `L(C ⋊ Lambda) = L^infinity(Ĉ) ⋊ Lambda`.
  - So Q1 makes every solvable-by-hyperlinear group hyperlinear, and every finite-by-hyperlinear
    group too. In particular every central extension of a hyperlinear group is hyperlinear.
  - Hence each of the following refutes Q1: a non-hyperlinear Kun--Thom wreath or Mihailova coset
    wreath, an `SL_3` module witness, an algebraic envelope with a hyperlinear actor, or a Schur/`Z/p`
    central-extension witness.
  - Q1 is at least as strong as the open problem of central-extension permanence for hyperlinearity.
  - Q2's used consequence, a non-CE crossed product, is already equivalent to NH under Q1.
- **Hosting the fixed non-CE relation decides Q1 at the host's actor (swarm-0917 w18, 2026-09-19).** See
  `nonce-relation-hosts-force-root-or-q1-failure`.
  - Suppose the Manzoor or property-(T) relation `R` is a class-bijective factor of a subrelation of an essentially
    free pmp action of `Lambda`. Then `L(R)` sits in a corner of that crossed product, so either `Lambda` is
    non-hyperlinear or Q1 fails at `Lambda`.
  - Two other placements give the same conclusion: a groupoid splitting `c : R -> Lambda` with `c(x, x') x = x'`
    (pad by Bernoulli), and regeneration of `R` by a `Lambda`-action with finite stabilizers (central corner).
  - Exactly: NH or not-Q1 holds iff some non-CE relation has such a host, iff some ergodic non-CE relation is
    generated by a free action.
  - The known Q1 groups (amenable-by-virtually-free, free) can host neither relation, even with infinite invariant
    measure. Non-treeability and the free-actor fence are special cases.
  - So refuting Q1 through the known non-CE relations is now a measured placement problem with no approximation
    content, `nonce-relation-admits-free-host`. Its actor must lie outside every class where Q1 is known.
  - Under Q1 the same placement names a non-hyperlinear group
    (`nonhyperlinear-via-q1-and-free-host-of-nonce-relation`).
- **Not attempted.** No mechanism is known that promotes microstates for `Gamma` to microstates for a covariant pair
  when the action is non-free and far from amenable. This is where a proof would have to start.
