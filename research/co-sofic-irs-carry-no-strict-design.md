---
rg: 2
id: co-sofic-irs-carry-no-strict-design
kind: claim
title: A co-sofic invariant random subgroup of a free group carries no strict automaton design, with a linear forward-to-reverse error bound
distinct_from:
  weakly-sofic-groups-are-surjunctive: that is surjunctivity of a group through approximation of its Cayley graph; this is the unimodular-network version, where forward and reverse tables vary from site to site and a quantitative inequality between their error densities passes to weak-* limits of finite Schreier graphs.
  separating-repetitive-amenable-schreier-families-force-soficity: that concerns fixed configurations on one amenable coset space of a group; this concerns designs carried by invariant random subgroups of a free group, with no group host and no amenability.
  surjunctive-groups-are-uniformly-quantitatively-surjunctive: that is a uniform quantitative form over a surjunctive group; this bounds the reverse-bad density by a constant times the forward-bad density over every finite Schreier graph, which is what lets site-varying tables pass to limits.
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

**ESTABLISHED** by `co-sofic-irs-carry-no-strict-design-proof`.

Let `D = (tau, sigma)` be a design of shape-dependent automata on Schreier graphs of `F_r`, with
alphabet `A` and radii `R_tau`, `R_sigma`. Put `r = R_tau + R_sigma`. Let `d_k` be the size of
the radius-`k` ball of the `2r`-regular tree. For an IRS `mu`, let `eps_D(mu)` be the probability
that the root is forward-bad, and `delta_D(mu)` the probability that it is reverse-bad (artifact
Section 2).

**Theorem.** Every co-sofic IRS `mu`, i.e. every weak-* limit of IRS of finite `F_r`-sets, satisfies

    delta_D(mu) <= ( d_(R_tau) + d_(2r) |A|^(d_r) ln|A| ) eps_D(mu).

In particular no co-sofic IRS carries a strict design, since a strict design has `eps = 0 < delta`.

- The inequality defines a closed convex set of IRS.
- On a vertex-transitive index set `eps` is `0` or `1`, so the inequality has content only once
  homogeneity is dropped.
- For normal `N`, `delta_N` is co-sofic iff `F_r/N` is sofic. With
  `atomic-irs-strict-designs-are-nonsurjunctive-quotients` this recovers Gromov-Weiss for finitely
  generated sofic groups.

Full proof: artifact Section 4.
