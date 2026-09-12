---
rg: 2
id: popa-bernoulli-cocycle-superrigidity
kind: claim
title: Cocycles of Bernoulli actions of w-rigid groups into U_fin groups are cohomologous to homomorphisms
distinct_from:
  icc-property-t-not-w-star-superrigid: that records a W*-superrigidity failure for ICC property (T) groups; this is Popa's cocycle superrigidity for their Bernoulli actions, a statement about measurable cocycles.
  finite-rank-superrigid-cocycles-cannot-cancel-fixed-points: that assumes a cocycle is cohomologous to a homomorphism and derives a trace obstruction on non-free actions; this is the literature theorem supplying that hypothesis for Bernoulli actions.
artifacts:
  - research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md
---

ESTABLISHED by citation. Let `G` be a countable group containing an infinite normal subgroup `H` with
`(G, H)` having the relative property (T), for instance any infinite group with property (T). Let
`G -> (X_0, mu_0)^G` be a Bernoulli action with nontrivial base. Let `V` be a closed subgroup of the
unitary group of a separable II_1 factor; this class `U_fin` contains every countable discrete group
and every second countable compact group. Then every measurable cocycle `c: G x X -> V` is
cohomologous to a homomorphism `G -> V`.

Source: S. Popa, *Cocycle and orbit equivalence superrigidity for malleable actions of w-rigid
groups*, Invent. Math. 170 (2007), 243–295, Theorem 0.1.

**Trust surface.** Statement-level import. The theorem number and the precise definition of `U_fin`
were not re-verified against the PDF in this lane. The only consumer so far,
`kazhdan-map-bernoulli-finite-extensions-are-trivial`, uses finite targets `V = Sym(n)` only.
