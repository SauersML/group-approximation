---
rg: 2
id: fpbs-central-amenable-relative-threshold-is-pu
kind: claim
title: With an infinite central subgroup every infinite amenable subgroup has relative threshold p_u, so no subgroup gives a weaker relative gap
distinct_from:
  fpbs-amenable-wq-normal-pu-is-relative-pc: that equates p_u with the relative threshold of one amenable wq-normal subgroup; this shows that when the group has an infinite central subgroup, every infinite amenable subgroup has relative threshold p_u, wq-normal or not, and that a relative gap along a subgroup implies one along each of its infinite amenable subgroups.
  fpbs-relative-gap-along-any-subgroup-separates: that proves a relative gap along any infinite subgroup separates the thresholds; this shows that, given an infinite central subgroup, the premise along any subgroup containing an infinite amenable subgroup is never weaker than p_c < p_u itself.
  fpbs-bs-iff-finite-relative-susceptibility: that is the equivalence along one amenable wq-normal subgroup; this shows that changing the subgroup either reproduces that equivalence or gives a stronger premise, so the criterion cannot be weakened by the choice of subgroup.
artifacts:
  - research/artifacts/fpbs-f2xz-rigid-relative-gap-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated, `G = Cay(Gamma,S)` any
Cayley graph, and suppose `Gamma` has an infinite central subgroup `C`. Write
`p_c(I;G)` for Hutchcroft--Pan's relative threshold: the infimum of the
parameters at which a cluster meeting `I` in an infinite set exists almost
surely.

1. **Monotonicity.** For infinite subgroups `I <= J`, `p_c(J;G) <= p_c(I;G)`.
2. **Amenable subgroups.** Every infinite amenable subgroup `A <= Gamma` has
   `p_c(A;G) = p_u(G)`.
3. **No weaker premise.** Let `I <= Gamma` be infinite and contain an infinite
   amenable subgroup `A`. Then `p_c(G) < p_c(I;G)` implies
   `p_c(G) < p_c(A;G) = p_u(G)`. If `I` is amenable, `p_c(G) < p_c(I;G)` is
   equivalent to `p_c(G) < p_u(G)`.

So on these graphs the relative-gap criterion
`fpbs-relative-gap-along-any-subgroup-separates` is at best equivalent to the
goal:
* along an infinite amenable subgroup the premise is exactly `p_c < p_u`;
* along any subgroup containing one, the premise is at least as strong.

If `Gamma` is torsion-free, every infinite subgroup contains `Z`, so this covers
every infinite subgroup.

**Scope.** Every Cayley graph of `F_n x Z`, including the rigid graph
`Cay(F_2 x Z, {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}^±)` whose automorphism
group is discrete. Also braid groups, spherical Artin groups and central
extensions by `Z`. On these graphs no choice of thin subgroup yields an easier
target: not a line `<(g,k)>`, not a free factor, not `F_2 x {0}`.

This is an obstruction to a strategy. It refutes no claim and settles no case
of `p_c < p_u`. The proof is in
`fpbs-central-amenable-relative-threshold-is-pu-proof`.
