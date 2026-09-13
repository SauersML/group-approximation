---
rg: 2
id: fpbs-line-independent-twisted-levels-disconnected
kind: claim
title: Twisted level graphs whose open levels are independent across fibre lines, with any dependence along each line, are almost surely disconnected at small density
distinct_from:
  fpbs-twisted-level-percolation-disconnected-at-low-density: that assumes every pair (u, m) is open independently; this allows arbitrary dependence along each t-orbit (periodic, Sturmian, odometer or any stationary row), requiring independence only across distinct fibre lines, with the same delta_0.
  fpbs-quotient-split-actions-have-cost-one: that uses an N-invariant set, the maximal correlation across lines, and proves cost one for split actions; this proves that correlation confined to single lines never connects the twisted return graph.
artifacts:
  - research/artifacts/fpbs/docs/twisted-levels-line-independent-disconnection.md
---

**ESTABLISHED** through `fpbs-line-independent-twisted-levels-disconnected-proof`.

**Setting.**
- `Gamma = N semidirect_phi Z` is torsion-free and word-hyperbolic, with `t` generating `Z` and `t u t^-1 = phi(u)`.
- `S` is a finite symmetric subset of `N \ {e}`.
- `delta_0 = delta_0(Gamma, t, S)` is the constant of `fpbs-twisted-level-percolation-disconnected-at-low-density`.

**Field hypotheses (LI).** A random field `omega : N x Z -> {0,1}` satisfies (LI) with density `delta` when:
1. its rows `omega(u, .)`, `u in N`, are independent;
2. its law is invariant under right translation `(u, m) -> (u w, m)`, `w in N`;
3. `P(omega(u, m) = 1) <= delta` for every pair.

Dependence inside a row is unrestricted. `T_omega` is the graph on `N` with edges `{u, phi^-m(s) u}` for open `(u, m)` and `s in S`.

**Claim.**
1. If `omega` satisfies (LI) with `delta < delta_0`, then `P(e <-> s in T_omega) < 1` for every `s in S`, and `T_omega` is almost surely disconnected.
2. **Co-induced actions.** Let `T` be an essentially free p.m.p. action of `Z` on `(Z, nu)`, and `Gamma` act by the co-induced action on `{f : Gamma -> Z : f(t h) = T f(h)}`, with product measure on `f|_N` and `(g.f)(h) = f(h g)`. This action is essentially free and ergodic. For Borel `B ⊆ Z` with `nu(B) < delta_0`, put `A = {f : f(e) in B}`. Then the transport graphing `{t} ∪ {s|_A : s in S}` does not generate the orbit relation.
3. **Bernoulli shift.** In the Bernoulli shift of `Gamma` on `[0,1]^Gamma`, take any Borel `A` that is measurable with respect to the coordinates on `<t>` and has `mu(A) < delta_0`. Then the transport graphing does not generate. This includes bases of Rokhlin towers for the `t`-shift of `x|_<t>`, and pullbacks of Sturmian or odometer factors of that process.

**Consequence.** Correlating open levels along `t`-orbits cannot rescue the transport graphing. In the Bernoulli shift a working set must correlate openness across fibre lines. It cannot do so through a factor on which `N` acts trivially (`fpbs-quotient-split-not-bernoulli-contained`). The remaining statement is the open claim `fpbs-cross-line-correlated-transport-set-generates`.

**Not settled.** `fpbs-hyperbolic-3-manifold-groups-fixed-price-one` stays OPEN. Sets that correlate rows are not covered. The artifact records why block factors across rows give no uniform bound.

No novelty or priority is claimed. The proof modifies only the probability step and the 0-1 law of main's disconnection proof.
