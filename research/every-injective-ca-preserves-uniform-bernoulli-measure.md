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
* **Mass transport on trees (gk-p-bernoulli-mass, 2026-09-12).** Over free groups the
  claim holds with no finite model: `free-group-injective-ca-preserve-bernoulli-via-f-invariant`.
  - Bowen's f-invariant agrees on `mu` and `tau_* mu`.
  - Splitting monotonicity plus submodularity on balls, with the tree identity
    `|B_n| - sum_i |B_n ∩ s_i B_n| = 1`, forces uniform ball laws. That identity is the
    Cayley tree's mass-transport balance in entropy form.

  Where it stops, per Section 5 of that artifact:
  - *Two-cells.* Face terms of an Euler functional need the three-set
    inclusion–exclusion bound, which fails on duplicated coordinates: one bit copied to
    three sites gives `log 2 > 0`. Duplication is exactly the redundancy of a strict
    image.
  - *Kazhdan hosts.* They have FA, so there is no tree index structure. The coordinate
    partition does not generate for a free subaction.
  - *Unimodularity.* Bijective translations are what balance the edge count.

  The f-invariant is partition-bounded, so on nonsofic hosts saturating any such
  invariant is at least as strong as INF (`rokhlin-entropy-is-the-largest-partition-bounded-invariant`).
* **Invariants of the image (gk-p-bernoulli-ergodic, 2026-09-12).** No isomorphism invariant can
  separate the image measure from the uniform measure. A strict automaton is a measure conjugacy
  onto its image, so Koopman spectral data, strong ergodicity, mixing of all orders, weak
  equivalence, cost, `l^2`-Betti numbers and every entropy agree
  (`measure-conjugacy-invariants-cannot-certify-surjectivity`).
  - Architectures that saturate a partition-bounded invariant reduce to maximal Bernoulli Rokhlin
    entropy (`rokhlin-entropy-is-the-largest-partition-bounded-invariant`).
  - Any other proof must use coordinate data together with the group structure of the index set:
    window laws, completion counts, and block-code radii in both directions. Section 3 of
    `research/artifacts/conjugacy-invariants-and-partition-bounds-2026-09-12.md`.
  - The functional asked for in gk-decoder-fiber's handoff is at most `log |A|`, equal at the
    uniform measure, and strictly smaller at every strict image. An isomorphism invariant takes
    equal values at the uniform measure and at every strict image. So for an invariant, "strictly
    smaller at every strict image" is equivalent to "no strict automaton exists", and proving it
    restates the conclusion (scope as corrected by gk-vf-positive). A useful functional must read
    the coordinate partition, as Shannon window entropies do.
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
* **Window fibers and the decoder (w3-bern-window, 2026-09-12).** Balance at a window is a one-sided
  fiber bound: no fiber above the average `q^(|EM| - |E|)` (`window-balance-is-a-fiber-upper-bound`).
  Injectivity supplies that bound only up to the boundary factor `q^(|d_N E|)`
  (`decoder-window-fiber-bound-loses-exactly-the-boundary`). The factor has zero density on amenable
  groups, which is Gromov--Weiss in counting form, and positive density on nonamenable groups;
  averaging over translates or invariant random windows keeps the density.
  - The three per-window relations: translation totals (unimodularity), the decoder bound
    (injectivity), and zeros at Gardens of Eden (strictness). The end-fixing tree drops the first;
    pre-injective non-surjective automata over nonamenable groups drop the second (Bartholdi--Kielak,
    recorded as a remark only).
  - Exact open step: the boundary-free decoder bound on a cofinal family of windows. At `E = {1}` the
    decoder bound is vacuous, matching `every-injective-ca-has-uniform-single-site-output-law`.
  - Artifact: `research/artifacts/window-balance-mass-transport-2026-09-12.md`.
