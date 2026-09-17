---
rg: 2
id: fpbs-morse-deficit-vanishes-for-full-presentations
kind: claim
title: Well-founded Morse matchings over short trivial words almost exhaust the cycle dimension of every Bernoulli Cayley graphing
artifacts:
  - research/artifacts/fpbs/docs/bernoulli-morse-collapse-criterion.md
  - research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md
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

**2026-09-17 (swarm-0917-w5-pull-fp-1): dual-forest matchings along a two-incidence edge class.** This proves (Q1),
and hence this claim, fixed price and `C(b) = 1 + beta_1`, for every infinite `<S | w^m>` in which some generator is
used exactly twice in `w`. See `fpbs-one-relator-twice-used-letter-fixed-price`.

- By Weinbaum the boundary cycles are embedded, so each `s`-edge lies on exactly two distinct cycles.
- The dual graph on cycles has component `<w,t><w>`. The Freiheitssatz gives an element of infinite order in
  `<w,t>`, so the components are infinite.
- Matching each cycle to the `s`-edge toward its parent in a BFS forest around sparse iid markers gives mass
  `(1 - eps)/m`. Mass transport makes the trees finite, and children of a matched edge are exactly its tree children.
- This reaches the proper-power ceiling `1/m` with the single relator `w^m`.

It does not reach the general claim, and dies as a general method at the incidence count. If every letter is used at
least three times, an `s`-edge has `k >= 3` incidences. A matched edge is then a child of the matched edges of all
`k - 1` other incident cells, so well-foundedness needs a Borel peeling of the incidence hypergraph, which nothing
here supplies. Kazhdan groups, and one-relator groups in which every letter repeats, are untouched. Artifact:
`research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md`.
