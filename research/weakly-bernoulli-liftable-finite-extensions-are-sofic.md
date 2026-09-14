---
rg: 2
id: weakly-bernoulli-liftable-finite-extensions-are-sofic
kind: claim
title: A finite extension of a sofic group is sofic when some action lifted across the kernel is weakly contained in a Bernoulli shift of the base
distinct_from:
  weakly-bernoulli-liftable-action-makes-extension-sofic: that is the central case over a finitely presented base, through torsors over a presentation; this drops centrality and finite presentation, through microstates of the lifted action carrying the extension cocycle.
  finite-actions-with-vanishing-class-norm-make-extension-sofic: that gets soficity from exact finite actions with small-support torsor cochains over a residually finite base; this gets it from one weakly Bernoulli liftable action over any sofic base.
artifacts:
  - research/artifacts/gk3-rokhlin-tester-2026-09-14-part2.md
---

**ESTABLISHED (unreviewed)** by `weakly-bernoulli-liftable-finite-extensions-sofic-proof`.

Let `Q` be sofic and `N ◁ W` finite with `W/N ≅ Q`. Suppose some p.m.p. `Q`-action `Y_0 = X_0/N`, where `X_0` is a
free p.m.p. `W`-action, is weakly contained in the Bernoulli shift `[0,1]^Q`. Then `W` is sofic.

In particular, cases (i) and (ii) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift` produce only sofic groups
from sofic quotients:
- in case (i), `Y_0` is weakly contained in every free action, the Bernoulli shift among them;
- in case (ii), a finite-entropy Bernoulli shift is a factor of `[0,1]^Q`.

**Proof idea.**
- **Cocycle.** A Borel section of `X_0 -> Y_0` gives a cocycle `ν : W × Y_0 -> N` with
  `ν(ww', y) = c_w(ν(w', y)) ν(w, π(w')y)`, and `ν(m, y) = m` on `N`.
- **Microstates.** Bernoulli shifts over sofic groups have microstates over every sofic approximation, and weak
  containment transfers them to `Y_0`.
- **Models.** Reading `ν` from the microstate labels gives permutations `τ_n(w)(m, v) = (c_w(m) ℓ(v)_w, σ_n(π(w))v)` of
  `N × V_n`. They are almost multiplicative because the cocycle identity is a pattern condition, and almost free
  because `ν(m, ·) = m`.

Section 2 of the part 2 artifact.

**Model test.**
- **Hypothesis side.** A split `N ⋊ Q` acting on `N × [0,1]^Q` has `Y_0 = [0,1]^Q`, and it is sofic.
- **Conclusion side.** Over the Gohla–Thom lattices no such `Y_0` exists
  (`gohla-thom-lattices-no-weakly-bernoulli-liftable-action`), consistent with their conditional nonsoficity.
