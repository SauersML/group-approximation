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
