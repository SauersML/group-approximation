---
rg: 2
id: central-d8-mark-radical-equals-seed-radical
kind: claim
title: The central D8 mark lies in the hyperlinear radical exactly when its seed does
distinct_from:
  central-d8-seed-preserves-hyperlinearity: that is the group-level statement that the marked group is hyperlinear iff the base is; this is the element-level statement that the mark J is in the hyperlinear radical iff the seed b is, with an explicit J=-1 model otherwise.
  infinite-character-interface-is-marked-radical-certificate: that shows a uniform interface puts J in the radical of the marked group; this transfers that membership back to the seed in the unmarked base and gives the exact converse.
  infinite-character-actor-kills-fd-mark: that kills J in exact finite-dimensional representations; this concerns homomorphisms into tracial matrix ultraproducts, where J survives as -1 as soon as the seed survives.
artifacts:
  - research/artifacts/seed-radical-transfer-2026-09-16.md
---

**ESTABLISHED** by route `central-d8-mark-radical-proof`. No novelty is claimed.

Let `G` be a countable group, `b in G` with `b^2 = 1`, and

```text
P(G,b) = < G, z, J | z^2 = J^2 = 1, J central, [b,z] = J >.        (CDS1)
```

**Theorem.** `J in Rad_hyp(P(G,b))` iff `b in Rad_hyp(G)`. If `b notin Rad_hyp(G)`, there is a homomorphism
`Theta : P(G,b) -> U(prod_omega' M_(D_k))` into a tracial matrix ultraproduct with `Theta(J) = -1` exactly.

The proof shifts the seed trace into `[0,1)` by adding a trivial summand, then takes tensor powers until the trace
of `b` tends to zero. It rounds each level to an exactly balanced involution, using
`|lambda - sgn(lambda)| <= |lambda^2 - 1|`, and adjoins the exact Pauli partner
`Z = I (x) [[0,1],[1,0]]`.

**Consequence for the infinite-character route.** This remark combines the theorem with the ESTABLISHED nodes
`infinite-character-interface-is-marked-radical-certificate` and `hyperlinear-radical-presentation-compactness`; it
is not part of the direct route. For an actor--module base `G = M rtimes A` with involutive seed `m_0`, the
qualitative content of the terminal output `(ICR2)` (existence of some finite-window modulus bounding
`||J(U) - I||_2`, not necessarily one factoring through `E_act` and `eta_seed`) is equivalent to the element-level
statement

```text
m_0 in Rad_hyp(M rtimes A),
```

and then the whole normal closure of `m_0` lies in the radical. This is non-effective in one direction, by
`hyperlinear-radical-presentation-compactness`. The D8 mark adds nothing to the matrix-microstate problem, even at
the level of individual elements. Any proof of `infinite-character-actor-word-energy-interface` for a given host
must place the unmarked seed itself in the hyperlinear radical of the unmarked base.
