---
rg: 2
id: popa-bernoulli-cocycle-superrigidity
kind: claim
title: Cocycles of s-malleable actions of w-rigid groups, such as diffuse-base Bernoulli shifts, into U_fin groups are cohomologous to homomorphisms
distinct_from:
  icc-property-t-not-w-star-superrigid: that records a W*-superrigidity failure for ICC property (T) groups; this is Popa's cocycle superrigidity for their Bernoulli actions, a statement about measurable cocycles.
  finite-rank-superrigid-cocycles-cannot-cancel-fixed-points: that assumes a cocycle is cohomologous to a homomorphism and derives a trace obstruction on non-free actions; this is the literature theorem supplying that hypothesis for Bernoulli actions.
artifacts:
  - research/artifacts/kazhdan-superrigidity-bernoulli-extensions-2026-09-12.md
---

ESTABLISHED by citation. Let `G` be a countable group containing an infinite normal subgroup `H` with
`(G, H)` having the relative property (T), for instance an infinite group with property (T) and
`H = G`. Let `G ↷ (X, mu)` be an s-malleable measure-preserving action whose restriction to `H` is
weakly mixing. The standard example is the Bernoulli action `([0,1], Leb)^G` with diffuse base. Let
`V` be a closed subgroup of the unitary group of a separable II_1 factor; this class `U_fin` contains
every countable discrete group. Then every measurable cocycle `c: G x X -> V` is cohomologous to a
homomorphism `G -> V`.

Source: S. Popa, *Cocycle and orbit equivalence superrigidity for malleable actions of w-rigid
groups*, Invent. Math. 170 (2007), 243–295, Theorem 0.1.

**Trust surface.** Statement-level import. The theorem number, and the precise definitions of
s-malleability and of `U_fin`, were not re-verified against the PDF in this lane. Remark 4.3 of the
artifact would also need compact groups in `U_fin`; nothing landed depends on that remark.

**Scope correction (2026-09-12).** The first version of this node stated the theorem for Bernoulli
actions with an arbitrary nontrivial base. gk-vf-positive (Section 12 of
`research/artifacts/gk-vf-positive-verification-2026-09-12.md`) flagged that the abstract-level
statement concerns s-malleable actions, so coverage of atomic bases such as `A^G` would have to be
read at source. This node now imports only the s-malleable form, and that is the only form consumed:
`kazhdan-map-bernoulli-finite-extensions-are-trivial` reduces an arbitrary base to `([0,1], Leb)^G`
by multiplying with an independent Bernoulli factor (artifact Theorem 4.1, step 0), and uses only
finite targets `V = Sym(n)`.
