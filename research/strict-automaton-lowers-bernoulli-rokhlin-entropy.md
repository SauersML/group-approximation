---
rg: 2
id: strict-automaton-lowers-bernoulli-rokhlin-entropy
kind: claim
title: A strict injective automaton over a group lowers the Rokhlin entropy of its amplified uniform Bernoulli shifts
distinct_from:
  sofic-radical-localizes-garden-of-eden-windows: that runs Gromov--Weiss counting along almost-multiplicative permutation models; this uses no finite model and bounds an isomorphism invariant of the Bernoulli shift itself.
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse pair into a strict linear automaton; this turns any strict automaton into an entropy deficit of Bernoulli shifts.
  infinite-rokhlin-supremum-forces-surjunctivity: that imports Seward's per-group implication from an infinite Rokhlin supremum to surjunctivity; this is a self-contained quantitative proof of the strictness half, with explicit constants, from which strict-automaton-bounds-rokhlin-supremum reads a finite supremum.
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Let `G` be a countably infinite group and `A` a finite alphabet with
`q = |A| >= 2`. Let `nu` be an invariant probability measure on `A^G` that is
isomorphic to the uniform Bernoulli shift and misses a cylinder `[p]`,
`p in A^Omega`. For example `nu = tau_* mu_A` for an injective, non-surjective
cellular automaton `tau`. Put `delta = -log(1 - q^-|Omega|)` and
`D = |Omega Omega^-1|`. Then for every `k >= 1`

    h^Rok_G((A^k)^G, uniform) <= k (log q - delta/D) + log 3.

`h^Rok` is Rokhlin entropy: the infimum of the Shannon entropies of generating
countable partitions. It is an isomorphism invariant. Window-counting entropy is
not one over nonamenable groups
(`window-entropy-deficits-are-not-isomorphism-invariant`).

Consequences:

* The per-copy limit `rho_q(G) = lim_k h^Rok((A^k)^G)/k` is at most
  `log q - delta/D`.
* The Rokhlin entropy of `(A^k)^G` is strictly below its base entropy `k log q`
  once `k > D log 3/delta`.
* Contrapositive: if `h^Rok((A^k)^G) = k log q` for every `k`, every injective
  automaton on `A^G` is surjective. For `q = p^n`, `F_p[G]` is stably finite
  through linear automata.

**ESTABLISHED 2026-09-12** by
[[strict-automaton-lowers-bernoulli-rokhlin-entropy-proof]].
