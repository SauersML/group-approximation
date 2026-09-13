---
rg: 2
id: quotient-restriction-deficit-proof
kind: route
title: Equivariant injections send invariant configurations injectively to invariant configurations, giving an automaton over the quotient or a count
target: quantitative-surjunctivity-constants-lift-from-quotients
requires: []
artifacts:
  - research/artifacts/quantitative-surjunctivity-residue-2026-09-12.md
---

Proposition 2.1 and Corollaries 2.2–2.4 of the artifact.

- **Restriction.** An injective automaton `Phi` from `(B^n x D^j)^G` into `Y^n x (D^(j'))^G` commutes with
  translations. So it maps `Fix_N` into `Per_N(Y)^n x Fix_N((D^(j'))^G)`.
- **Quotient.** On `Fix_N = B^(G/N)` it is an injective automaton over `G/N` into `Y_N^n x (D^(j'))^(G/N)`, which a
  constant of `Y_N` excludes.
- **Counts.** Constants give `|B|^n |D|^j <= c_Y^n |D|^(j')`. A subgroup `H` of finite index `m` gives
  `(|B|^n |D|^j)^m <= |Y cap Fix_H|^n |D|^(j' m)`.
- **Residually finite case.** Take `H` normal with `W` injecting into `G/H`. Periodic points avoid the pattern on
  at least `m / |W|^2` disjoint windows.

Independently re-derived 2026-09-12 by w4-vf-positive-b: PASS (Section 8.2 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`).
- **Re-derived:** the restriction to `Fix_N`, the constant and periodic counts, and the greedy bound of at least
  `m / |W|^2` disjoint windows.
- **Note:** since `82a4dbf6c`, the residue bullet on the claim follows from the restriction step and the definition.
  Only its sub-bullet on sofic quotients uses the sofic count, which this route rightly does not cover.
