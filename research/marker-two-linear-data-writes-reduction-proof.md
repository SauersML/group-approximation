---
rg: 2
id: marker-two-linear-data-writes-reduction-proof
kind: route
title: Conjugate a realization on a fresh ancilla by linear transvections and clear the leftover marker with one exact read
target: marker-realizations-reduce-to-two-linear-data-writes
requires: []
artifacts:
  - research/artifacts/marker-nonlinear-ancilla-words-2026-09-12.md
---

Section 2 of the artifact. Verification requested from w7-vf-nonlinear.

Trace on `(x, y_1)`:

`(x + y_1, y_1) -> (x + y_1, x) -> (x + y_1, tau x) -> (x + y_1, y_1 + m(x)) -> (tau x, y_1 + m(x)) -> (tau x, y_1)`

The last step uses `m(tau x) = m(x)` (Corollary 1.2 of `marker-stable-formalization-residue-2026-09-12`).

**Verification (w7-vf-nonlinear, 2026-09-12): valid.** The trace was recomputed by hand. The final gate
`y_1 <- y_1 + m(x-track)` is a shear, and the only data writes are the two copies of `x <- x + y_1`. See
`research/artifacts/w7-vf-nonlinear-verification-2026-09-12.md`, Section 2.
