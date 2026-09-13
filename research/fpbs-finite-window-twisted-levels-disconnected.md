---
rg: 2
id: fpbs-finite-window-twisted-levels-disconnected
kind: claim
title: Transport sets that read a finite window of Bernoulli coordinates do not generate below a threshold exponential in the window, and small generating sets can be taken local
distinct_from:
  fpbs-line-independent-twisted-levels-disconnected: that allows any dependence along each t-orbit but needs open levels independent across fibre lines, with the uniform threshold delta_0; this allows arbitrary correlation across finitely many lines through a finite window W, with the window-dependent threshold delta_0^|W^-1 W|.
  fpbs-twisted-level-percolation-disconnected-at-low-density: that assumes every pair (u, m) is open independently; this concerns Borel sets of the Bernoulli shift that read a finite window, whose open levels may be correlated across fibre lines.
artifacts:
  - research/artifacts/fpbs/docs/cross-line-transport-sets-finite-windows.md
---

**ESTABLISHED** through `fpbs-finite-window-twisted-levels-disconnected-proof`.

**Setting.**
- `Gamma = N semidirect_phi Z` is torsion-free and word-hyperbolic, with `t` generating `Z` and `t u t^-1 = phi(u)`.
- `S` is a finite symmetric generating set of `N` with `e ∉ S`.
- `delta_0 = delta_0(Gamma, t, S)` is the constant of `fpbs-twisted-level-percolation-disconnected-at-low-density`.
- `mu` is the product measure on `[0,1]^Gamma`, with `(g.x)(h) = x(h g)`.
- A Borel `A` is `W`-local, for a finite `W ⊆ Gamma`, when it is measurable with respect to `x|_W`. Put `D(W) = |W^-1 W|`.
- `E_s^r(A)` is the set of `x` that no path of at most `r` edges of `{t} ∪ {s'|_A : s' in S}` joins to `s x`.

**Claim.**
1. **Finite windows.** Let `A` be `W`-local with `mu(A) < delta_0^D(W)`. Then the twisted return graph of `A`, from item (1) of `fpbs-twisted-level-graph-generates-cyclic-extension`, is almost surely disconnected. So the transport graphing `{t} ∪ {s|_A : s in S}` does not generate the orbit relation.
2. **Reduction to finite windows.** The following are equivalent:
   - (a) for every `epsilon > 0` some Borel `A` with `mu(A) < epsilon` has a generating transport graphing;
   - (b) the same with `A` local;
   - (c) for every `epsilon > 0` there are `r` and a Borel `A` with `mu(A) + sum_(s in S) mu(E_s^r(A)) < epsilon`.
3. **Window size.** If a `W`-local `A` has a generating transport graphing, then `D(W) >= log(1/mu(A)) / log(1/delta_0)`.

**Consequence.** Statement (a) is the open claim `fpbs-cross-line-correlated-transport-set-generates`. A proof of it may use local sets, and their windows must grow like `log(1/mu(A))`.

**Not settled.**
- The threshold depends on the window. So this neither refutes the open claim nor invalidates route `fpbs-3-manifold-fixed-price-via-correlated-transport-sets`.
- Section 4 of the artifact shows that clumped sets open exponentially many paths together with one rare event. These include Rokhlin-type bases, slice percolation clusters and rare patterns in a ball. So per-witness first moments cannot give a uniform threshold.
- `fpbs-hyperbolic-3-manifold-groups-fixed-price-one` stays OPEN.

No novelty or priority is claimed. The proof modifies only the probability step of main's disconnection proof and adds a standard finite-range localization.
