---
rg: 2
id: monotone-binary-injective-rules-are-copies-proof
kind: route
title: Sensitivity of constant backgrounds sandwiches a monotone rule between two coordinates
target: monotone-binary-injective-rules-are-copies
requires: []
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Artifact, Section 2, Lemmas 4 and 5.

- **Constant backgrounds.** Let `x` be constant `c`, and let `x'` differ from it at site `1` only.
  Each output reading site `1` sees it at exactly one address, with `c` everywhere else. So injectivity
  needs some `m` with `mu(c at M \ m, d at m) != mu(c at M)`.
- **Background `0`.** Monotonicity gives `mu(0) = 0`, and some `t` with `mu(e_t) = 1`. So
  `mu >= x_t`.
- **Background `1`.** Monotonicity gives `mu(1) = 1`, and some `t'` with `mu(1 - e_t') = 0`. So
  `mu <= x_t'`.
- **Conclusion.** Evaluating at `e_t` gives `t = t'`, so `mu = x_t`.
- **Nonincreasing rules.** These are the same argument with the output complemented.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 8).
