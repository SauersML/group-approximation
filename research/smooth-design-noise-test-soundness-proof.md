---
rg: 2
id: smooth-design-noise-test-soundness-proof
kind: route
title: Substitute design moments and pull-back smoothness at the four places BKM use uniform pairings
target: noise-test-sound-on-smooth-design-rich-inputs
requires: []
artifacts:
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

Section 4 of the artifact.

* **Design moments.** Right labels are randomized, which changes no event used,
  so a `t`-wise uniform family fools every degree-`t` function on the 2-to-1
  maps domain. The conditioning `pi(2n-1)=pi(2n)=n` has degree one.
  `G[pi] = I_n[g|_pi]` has degree `2d`, because `1_E(p_pi^(-1)(x))` does not
  depend on `pi`, and `G^4` has degree `8d`. So Lemma 4.6's first moment and
  Lemma 4.9's fourth moment agree with the uniform measure, and the Markov step
  gives the same tail. Lemma 4.10's pair averaging uses degree-one probabilities.
* **Smoothness.** The high-degree term in Lemma 4.12 is an expectation under the
  pull-back distribution, bounded by `C_0 ||f^(>d)||_2^2`. The imbalanced term
  is family independent.
* **Unchanged.** Lemmas 4.7, 4.8, 4.11 and Theorem 2.13 concern the uniform
  measure or `f` alone. Lemma 3.1 and Section 5.2 compose these verbatim.
