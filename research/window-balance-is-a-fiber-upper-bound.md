---
rg: 2
id: window-balance-is-a-fiber-upper-bound
kind: claim
title: An automaton preserves uniform Bernoulli measure exactly when no window fiber exceeds the average size
distinct_from:
  every-injective-ca-preserves-uniform-bernoulli-measure: that is the open universal statement for injective automata; this is an exact one-sided reformulation of preservation, automaton by automaton and window by window, with no injectivity assumed.
  every-injective-ca-has-uniform-single-site-output-law: that is the single-site law for every injective automaton, equivalent to the goal through an anchor construction; this reformulates balance at an arbitrary window as a fiber upper bound, for one automaton.
artifacts:
  - research/artifacts/window-balance-mass-transport-2026-09-12.md
---

**ESTABLISHED** (artifact Section 2, route `window-balance-fiber-upper-bound-proof`).

Let `tau` be a cellular automaton on `A^G` with memory `M`, `q = |A|`, and for a finite window `E`
and `p in A^E` let `c_E(p)` be the number of `q' in A^(EM)` with `tau(q')|_E = p`. Then the image of
the uniform product measure is uniform on `E` if and only if

    c_E(p) <= q^(|EM| - |E|)     for every p in A^E .

Balance at `E` implies balance at every subwindow. So `tau` preserves the uniform measure exactly
when this upper bound holds on a cofinal family of windows.

Consequence: any proof of Gottschalk through Bernoulli preservation needs only UPPER bounds on
fiber sizes. A Garden-of-Eden pattern is a zero fiber, which forces some other fiber on the same
window above the average.
