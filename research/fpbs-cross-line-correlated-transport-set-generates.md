---
rg: 2
id: fpbs-cross-line-correlated-transport-set-generates
kind: claim
title: The Bernoulli shift of a fibered hyperbolic 3-manifold group has transport sets of arbitrarily small measure that generate
distinct_from:
  fpbs-twisted-level-percolation-connected: that is connectivity of independent twisted level percolation, now refuted; this asks for some Borel set of small measure, necessarily correlating open levels across fibre lines, whose transport graphing generates.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that is fixed price for every extension by a bounded-cost normal subgroup; this is one explicit graphing family on one action of the fibered cyclic extensions.
artifacts:
  - research/artifacts/fpbs/docs/twisted-levels-line-independent-disconnection.md
---

**OPEN.** Let `M` be a closed hyperbolic 3-manifold fibering over the circle. Let `Gamma = pi_1(M) = N semidirect_phi Z`, with fibre group `N`, `t` generating `Z`, and `S` a finite symmetric generating set of `N`. Let `b_Gamma` be the Bernoulli shift on `[0,1]^Gamma`.

**Claim.** For every `epsilon > 0` there is a Borel `A ⊆ [0,1]^Gamma` with `mu(A) < epsilon` such that the transport graphing `{t} ∪ {s|_A : s in S}` generates the orbit relation of `b_Gamma`.

Equivalently, by item (1) of `fpbs-twisted-level-graph-generates-cyclic-extension`, the twisted return graph of `A` is connected for almost every point.

**Why it matters.** With that criterion, `fpbs-bernoulli-maximal-cost` and the fibered-cover transfer, it gives fixed price one for closed hyperbolic 3-manifold groups. See route `fpbs-3-manifold-fixed-price-via-correlated-transport-sets`.

## Attempts

- **Independent levels (2026-09-12).** These are dead: `fpbs-twisted-level-percolation-disconnected-at-low-density`.
- **Correlation along `t`-orbits only (2026-09-12, lane `fixed-price-correlated-levels`).** Also dead: `fpbs-line-independent-twisted-levels-disconnected`.
  - Every `A` read off one `t`-orbit of coordinates, with `mu(A) < delta_0`, gives a disconnected graph.
  - That covers Rokhlin tower bases, Sturmian and odometer codings of one coordinate line, and arbitrary stationary rows.
  - Bases and factors of the whole `t`-action that read several lines correlate rows, so they are not covered.
  - It also holds in every co-induced action. So a working `A` must correlate rows.
- **`N`-invariant sets.** These work in split actions (`fpbs-quotient-split-actions-have-cost-one`), but `b_Gamma` has no factor on which `N` acts trivially (`fpbs-quotient-split-not-bernoulli-contained`).
- **Block factors across rows.**
  - If `A` depends on `x|_(<t> F)` for a finite `F`, then `omega(u, m)` depends on the rows `phi^-m(v) u`, `v in F`.
  - A self-avoiding path with bounded excursion can meet the `F`-star of a single row at `O(l)` levels.
  - So the independent-witness extraction has no uniform dependency bound. At best a radius-dependent `delta_0(F)` follows, which does not rule out small sets that are non-local.
- **Mass transport and spectral gap.** Charging witnesses along shortest paths forces only path length `>~ log(1/delta)`. The spectral gap of the `N`-Bernoulli action forbids relatively almost invariant `A`, but chains `B ∪ t^k s B` escape it. There is no contradiction either way.
- **Pseudo-Anosov Markov partitions.** Boundary and lamination actions of `Gamma` are not p.m.p., so they don't give Borel sets of `b_Gamma` directly. No construction.
