---
rg: 2
id: injective-ca-product-trace-zero-one-law
kind: claim
title: The product trace sees an injective automaton's range projection as zero or one, never in between
distinct_from:
  split-ca-quantization-has-sharp-defect: that computes the norm distance of the range projection from the quasilocal algebra and the multiplicative defect of the compression; this computes the value of every product-trace extension on the range projection and the singularity of the image measure, and proves all trace-level compatibility premises equivalent to surjectivity.
  injective-ca-pullbacks-extend-to-matrix-observables: that is the open universal extension criterion; this is a per-automaton zero-one law showing that every trace-level weakening of that criterion is still equivalent to surjectivity.
artifacts:
  - research/artifacts/gottschalk-product-trace-zero-one-law-2026-09-12.md
---

Let `G` be infinite and `tau: A^G -> A^G` injective, with image `Y`, uniform
product measure `mu`, and `nu = tau_* mu`. Quantize on finite perturbations of
constant backgrounds as in `split-ca-quantization-has-sharp-defect`: `V` is the
encoder isometry, `P = VV*`, `Phi(O) = V* O V`, `A_G` the quasilocal algebra, and
`tr` its product trace.

- If `tau` is onto, then `nu = mu`, `P = I`, and `tr o Phi = tr`.
- If `tau` is not onto, then `mu(Y) = 0`, so `nu` is singular to `mu`. Every state
  on `B(H)` extending `tr` has value `0` on `P`, and `tr o Phi` is not tracial.

So the following are equivalent for each injective `tau`: onto; `nu = mu`;
`nu` absolutely continuous to `mu`; `nu` not singular to `mu`; some state
extending `tr` is positive on `P`; every such state is `1` on `P`; `tr o Phi` is
tracial; `Phi` is multiplicative; `P` commutes with `A_G`.

**Consequence for routes.** A Kaplansky-style argument through a shift-invariant
trace compatible with the encoder has no quantitative intermediate step: every
such quantity is exactly `0` for a strict encoder and exactly `1` for an onto
one. The Gromov--Weiss contradiction lives at logarithmic scale (entropy per
site), which a trace collapses. The square-alphabet hypothesis can enter a proof
only through a per-site logarithmic count.

**ESTABLISHED 2026-09-12** by `injective-ca-product-trace-zero-one-law-proof`.
