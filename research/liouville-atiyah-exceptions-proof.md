---
rg: 2
id: liouville-atiyah-exceptions-proof
kind: route
title: Clear denominators of algebraic approximants, restrict scalars with a well-conditioned basis, and bound small spectrum by the determinant conjecture
target: determinant-conjecture-excludes-liouville-atiyah-exceptions
requires:
  - atiyah-base-change-holds-off-a-countable-set
artifacts:
  - research/artifacts/atiyah-liouville-base-change-2026-09-12.md
---

Complete argument in `research/artifacts/atiyah-liouville-base-change-2026-09-12.md`.

* **Section 1, Lemmas 1-4.**
  - Lemma 1: small spectrum under the determinant conjecture,
    `log(1/eps) mu((0,eps)) <= n log+ ||r_A^* r_A||`.
  - Lemma 2: min-max for Hilbert `N(G)`-submodules.
  - Lemma 3: perturbation of kernels.
  - Lemma 4: upper semicontinuity of kernel dimension under norm convergence.
* **Section 2, Lemmas 5-6.**
  - Lemma 5: restriction of scalars along an order `O`, conjugate to the direct
    sum of the embeddings by a scalar similarity `S`. The small spectra of all
    conjugates together are bounded by the small spectrum of the integral model
    at a threshold scaled by `cond(S)^2`.
  - Lemma 6: `O` has a basis with `cond(S)` polynomial in the conjugate sizes of
    a spanning set, using successive minima and `|disc O| >= 1`.
* **Section 4, item 1.** Algebraic jumps of a family are finitely many. Kernel
  dimensions of companion matrices at algebraic points are integers, by the skew
  field of [[atiyah-base-change-holds-off-a-countable-set]], and independent
  eigenspaces bound their number.
* **Section 4, item 2.** For an approximant `xi` of degree `<= d` and height `H`,
  the integral model `a^D A(xi)` over `O_F[a xi]` has norm and conditioning
  polynomial in `H`. So the small spectrum of `A(xi)` in `(0, t]` is at most
  `C_5 log H / (log(1/t) - C_6 log H)`. Lemma 3 at `t = O(|z_0 - xi|^2)`, with the
  generic kernel at `xi`, gives `kappa(z_0) <= O(log H) / log(1/|z_0 - xi|)`,
  which rearranges to the exponent `C / kappa`.
* **Section 4, item 3.** An algebraically Liouville point violates item 2, so
  every family has `kappa = 0` there. QED
