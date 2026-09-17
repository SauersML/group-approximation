---
rg: 2
id: fpbs-morse-deficit-vanishes-for-full-presentations
kind: claim
title: Well-founded Morse matchings over short trivial words almost exhaust the cycle dimension of every Bernoulli Cayley graphing
artifacts:
  - research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md
distinct_from:
  fpbs-bernoulli-cycle-tail-compactness: that asks for compact near-minimizing sequences among arbitrary graphings; this restricts to subgraphings of one Cayley graphing organised by cell matchings, so it additionally contains subgraphing attainment (Q3 of the artifact) and can fail even if the cost-Betti equality holds
  fpbs-bernoulli-morse-collapse-criterion: that proves the criterion and the limit formula; this is the open assertion that the limit is zero
---

**OPEN.** For every infinite group `Gamma` with a finite generating set `S`,

```text
lim_{L -> infinity} m(P_L) = 0.
```

Here `m(P_L)` is the Morse deficit of the list of all words of length at most `L` that are trivial in `Gamma`, as
defined in `fpbs-bernoulli-morse-collapse-criterion`.

By Theorem B there, this is equivalent to `C_sub(S) = 1 + beta_1^(2)(Gamma)`: the Bernoulli cost excess over the
Betti number is approached by generating Borel subgraphings of the Cayley graphing `Phi_S`.

**Stronger forms.**

- Deficit zero for one finite presentation. This is (Q1) of the artifact, and follows from this claim together with
  depth compactness (Q2).

**Instances that hold.**

- `Z^2`, and products of groups whose factors have generators of infinite order.

**Instances that are open and fixed-price-relevant.**

- Infinite one-relator groups. Here the target mass is exactly the proper-power ceiling `1/m`.
- Infinite Kazhdan groups.

A counterexample would need a group whose Bernoulli cost excess is not reached inside a Cayley graphing, or one where
the cost–Betti equality fails.

## Attempts

**Route a near-optimal graphing through the Cayley graphing (Q3).** Take a near-minimizing graphing `Psi`, write each
`Psi`-edge as a Cayley path of length `l`, and keep only the Cayley edges used. The attempt dies at the cost count:
the union of the paths can cost up to `l` times `c(Psi)`, and nothing forces the paths to share edges.

**Commuting-direction chains, as in the product calibration.** Each removed `s`-edge is recovered along the orbit of
a generator `c` of infinite order, through a commutator relator `[s, c]`. This needs every generator to commute with
an element of infinite order, independent of the generator itself. The attempt dies for torsion-free hyperbolic groups,
including hyperbolic one-relator groups and hyperbolic Kazhdan groups. There centralizers are cyclic, so a commutator
`[s, c]` with `c` of infinite order forces `c` to be a power of the root of `s`. The `c`-orbit chain then runs along
the `s`-line itself, and the recovered edge reappears among its own descendants.

**2026-09-17 (swarm-0917-w5-fp-cycle-tail): prove the limit through one finite list (Q1 or Q2).** This dies at an l2
mass bound. `fpbs-morse-mass-bounded-by-relator-boundary-rank` proves `mu(M) <= rho(R) = dim cl im d2^R` for every
finite list, so `m(R) = gap(R) + A(R)` with the relation gap `gap(R) = z - rho(R)`. The gap is not always zero:
`fpbs-lamplighter-fixed-list-morse-attainment-fails` shows `gap(R) >= 2^-(K(R)+1)` for every finite list on
`Z/2 wr Z`, while this claim holds there (`C_sub = 1`). So no fixed finite list can witness the limit in general. What
survives: `gap(P_L) -> 0`, so this claim is equivalent to `lim_L A(P_L) = 0`, asymptotic attainment of the l2 rank by
well-founded matchings. For finite presentations `gap = 0`, and there (Q1) is exactly `A(R) = 0`. Artifact:
`research/artifacts/fpbs/docs/morse-l2-inequality-and-lamplighter-gap.md`.

**2026-09-17 (swarm-0917-w5-pull-fp-3, transplanter, group-rings): split the premise, and fix the Q3 route by
letting S grow.** The Q3 attempt above dies because it keeps the long edges as Cayley paths. Keep them as generators
instead:

- Split each piece of a near-optimal `Psi` into translations `x -> gamma.x`.
- Truncate to finitely many labels `F`.
- Back up the `S_0`-edges that are not yet connected. They have vanishing measure by dominated convergence.

This gives `C(a) = lim_R C_sub^a(B_R) = inf_S C_sub^a(S)` for every free action. So
`lim_R lim_L m_(B_R)(P_L) = C(b) - 1 - beta_1`, and at a fixed `S` this claim is exactly
`C(b) = 1 + beta_1` plus `(Q3)(S)`, where `(Q3)(S)` is upward closed in `S`.

Consequences:

- The Morse form of the cost–Betti target is lossless once `S` may grow.
- The only surplus of this claim over the target is attainment at small `S`, which no route to tail compactness needs.
- A failure at one `S` does not refute the target.

Group-rings transplant: `rho` is the von Neumann rank of `d2` over `Z Gamma`, so it does not depend on the action. All
action dependence sits in `A`. Ring tools produce division-closure pivots, not `±1` acyclic Morse pivots, since
`[[1,1],[1,-1]]` has rank 2 and no admissible pivot pair. So they stop at `A`.

Still open here: `(Q3)(S)` at small `S` for nonamenable, non-treeable groups. Test cases are `<S | w^m>` and
2-generator Kazhdan groups. Claim `fpbs-cost-is-limit-of-cayley-subgraphing-costs`; artifact
`research/artifacts/fpbs/docs/adapted-generating-sets-make-morse-deficit-lossless.md`.
