---
rg: 2
id: brin-thompson-mv-contains-a-distortion-element
kind: claim
title: For every m >= 2 the Brin-Thompson group mV contains an infinite-order element f with |f^N| = O(log^4 N) (Callard--Salo)
distinct_from:
  thompson-v-cyclic-subgroups-are-undistorted: that is undistortion of every infinite cyclic subgroup of V = 1V; this is the existence of a polylogarithmically distorted element in every mV with m >= 2, so the V statement does not extend.
---

**ESTABLISHED (import)** by `brin-thompson-mv-contains-a-distortion-element-citation`.

For every `m >= 2`, the Brin–Thompson group `mV` contains an element `f` of
infinite order whose word norm, with respect to a finite generating set of a
finitely generated subgroup containing it, satisfies `|f^N| = O(log^4 N)`.
Equivalently, `f` is a distortion element.

Source: A. Callard and V. Salo, *Distortion element in the automorphism group
of a full shift*, arXiv:2208.00685 (published in Ergodic Theory Dynam. Systems
44 (2024) 1757–1817), Theorem E. The element comes from the SMART reversible
Turing machine of Cassaigne, Ollinger and Torres-Avilés, through the embedding
of groups of reversible Turing machines in `mV` for `m >= 2` (their Theorem D
and the sentence before Theorem E).

**Consequences in this graph.**
- By item 1 of `heisenberg-in-nv-forces-drift-free-central-element`, `f` is
  drift-free: every `f`-invariant probability measure has zero mean offset.
  So for `m >= 2` the drift obstruction, which holds in `V`, cannot exclude
  `H_3(Z)`, `BS(1,k)` or `GL_d(Z)` (`d >= 3`) from `mV`.
- Their Corollary 1.2: `mV` does not act properly on a CAT(0) cube complex for
  `m >= 2`. Farley's proof of the Haagerup property of `V` therefore does not
  extend to `mV` (Problem 2.7). Kojima–Sheng, arXiv:2603.18410, Corollary 4.3,
  reach the same conclusion from infinitely divisible elements.
