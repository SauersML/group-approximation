---
rg: 2
id: every-injective-ca-preserves-uniform-bernoulli-measure
kind: claim
title: Every injective cellular automaton over every group preserves the uniform Bernoulli measure
distinct_from:
  injective-cas-over-leavitt-units-preserve-uniform-bernoulli: that is the same statement over the binary Leavitt unit group only; this quantifies over all groups and is equivalent to the goal.
  bernoulli-rokhlin-entropy-maximal-for-every-group: that is maximal Rokhlin entropy of Bernoulli shifts, an ergodic-theoretic hypothesis that implies surjunctivity with no known converse; this is preservation of the uniform measure by injective automata, equivalent to surjunctivity automaton by automaton.
artifacts:
  - research/artifacts/gottschalk-tree-calibration-and-bernoulli-preservation-2026-09-12.md
---

**OPEN.** For every group `G`, finite alphabet `A` and injective cellular
automaton `tau` on `A^G`, `tau_* mu_A = mu_A`, where `mu_A` is the uniform product
measure.

Two routes make it equivalent to `gottschalk-surjunctivity-conjecture`.
Automaton by automaton, it is the window balance: for every finite `Omega` and
every `p in A^Omega`, where `M` is the memory,

    #{ q in A^(Omega M) : tau(q)|_Omega = p } = |A|^(|Omega M| - |Omega|).

## Attempts

* **Sofic groups.** True, since Gromov--Weiss makes the automaton bijective and
  `bijective-ca-preserve-uniform-bernoulli-measure` applies. No information about
  nonsofic groups.
* **Entropy.** `strict-automaton-lowers-bernoulli-rokhlin-entropy` turns a failure
  into a Rokhlin entropy deficit. So the claim follows from maximal Bernoulli
  Rokhlin entropy for every group, which is open.
* **Fixed points of a normal subgroup.** Bijective on `Fix_H` when `H` is normal
  with surjunctive quotient. Empty on simple hosts.
* **Coinvariants `H_0(G; C(A^G, Z))`.** The missing cylinder's class dies, but the
  rank is infinite and the states are the invariant measures. No contradiction.
* **von Neumann kernel.** The kernel of the pullback is the invariant ideal of the
  image's complement, so ergodicity only says its measure is `0` or `1`. Vacuous, as
  in `injective-ca-product-trace-zero-one-law`.
* **Iterated images.** The attractor of `tau^n(A^G)` carries invariant Cesàro limit
  measures on which `tau` is a homeomorphism. No contradiction found.
* **Information transport.** Blocked by synergy (XOR); see the 2026-09-08
  pinning-control artifact. Kazhdan `H^1`-vanishing is untested.
* **Calibration.** Off groups the claim fails:
  `end-fixing-tree-symmetries-carry-strict-automata` gives a strict automaton on a
  homogeneous space of an amenable non-unimodular group. A proof must use that the
  index set is a group.
