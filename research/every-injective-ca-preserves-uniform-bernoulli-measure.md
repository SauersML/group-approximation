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
* **Digest (gk-archive, 2026-09-12).** **Proved:**
  - preservation forces surjectivity, automaton by automaton
    (`injective-measure-preserving-ca-is-surjective`);
  - bijective automata preserve the measure (`bijective-ca-preserve-uniform-bernoulli-measure`);
  - a failure lowers Rokhlin entropy (`strict-automaton-lowers-bernoulli-rokhlin-entropy`);
  - strict pairs carry positive-entropy flip lifts and infinitely many cellular sections
    (`strict-split-pairs-carry-positive-entropy-flip-lifts`,
    `strict-split-decoders-have-infinitely-many-sections`).

  **Dead:**
  - trace-level premises, which are zero-one (`injective-ca-product-trace-zero-one-law`);
  - zero fiber entropy (`xor-lift-of-bernoulli-has-positive-fiber-entropy`);
  - Bernoulli rigidity on Kazhdan hosts, since compressed coset shifts carry strict equivariant
    embeddings (`compressed-coset-shifts-carry-strict-equivariant-embeddings`,
    `kazhdan-bernoulli-rigidity-forces-surjective-embeddings` refuted);
  - every measure or spectral invariant of the image, because a strict automaton is a measure
    conjugacy onto its image.

  **Reductions:** it is enough to treat f.g. simple Kazhdan hosts
  (`gottschalk-reduces-to-fg-simple-kazhdan-groups`), and the Leavitt case is
  `injective-cas-over-leavitt-units-preserve-uniform-bernoulli`.

  **Exact open step:** use Curtis--Hedlund--Lyndon locality over the free regular action of the group
  itself. The tree calibration and the coset-shift embedding both show that nothing weaker than
  freeness plus group structure can suffice. Rephrased, the step is to prove the window balance for
  every finite window, or to find one window where it fails.
* **Untested ideas reported by lanes, not yet nodes (gk-archive, 2026-09-12).**
  - *gk-decoder-fiber, in its handoff to gk-rokhlin.* Look for a functional on invariant measures of
    `A^G`, for an arbitrary group, that
    - is at most `log |A|`;
    - equals `log |A|` at the uniform measure;
    - is monotone under injective automata, or additive over a decoder that has a cellular section.

    Test candidates on the flip-lift measure of `strict-split-pairs-carry-positive-entropy-flip-lifts`
    and on the strictly larger subshift of `strict-split-decoders-have-infinitely-many-sections`. Any
    such bound would also prove stable finiteness of `F_p[G]` for every group, so it must stay
    consistent with the Kaplansky lanes.
  - *gk-free.* Kazhdan `H^1`-vanishing as the missing cancellation in information transport. It is
    listed above as untested, and no lane has taken it.
