---
rg: 2
id: wave2-ghb7-phase-normalized-defect-is-controlled-by-centrality
kind: claim
title: Fixed-gap GHB7 tuples have phase-normalized relator defect comparable to relator centrality error with dimension-independent constants
distinct_from:
  hrf-ghb7-central-relator-models-round-strictly: That rounds exactly central relators to genuine representations; this allows approximate centrality but only eliminates scalar phases, leaving a quantitatively bounded nonscalar residual.
  hrf-ghb7-scalar-expander-rounding: That asks for genuine flexible rounding of all fixed-gap tuples; this proves an error comparison and does not remove the residual noncentral defects.
artifacts:
  - research/artifacts/hyperbolic-rf-wave2-matching-2026-09-20.md
---

For a doubled GHB7 tuple W with scalar conjugation gap c>0, let delta
be the maximum plus-relator normalized-HS defect and kappa the maximum
commutator norm of a plus relator with any doubled generator. There
are positive presentation-dependent constants delta_* and B_c, independent
of matrix dimension, such that when delta<delta_*, scalar phases alpha_s
applied to both copies give

    delta(alpha W)<=B_c kappa,
    max_s |alpha_s-1| <=(pi/7)delta.

Scalar gap, kappa and copy-equality defects are preserved exactly.
Consequently the minimum delta_phase over all scalar rephasings obeys

    kappa/2 <=delta_phase<=B_c kappa.

The proof gives delta_*=min(1/4,sin(pi/(2*2401))) and
B_c=(2c)^(-1/2)(1+pi K/(2*2401)), where K is the finite certificate
constant explicitly defined in Section 1 of the artifact. Its numerical
value is not computed; its existence follows from the proved multiplier
bound, not from a new assumption.

If the three plus generators already have exact seventh powers I,
then delta<=B_c kappa before rephasing. Thus delta<delta_* and
kappa<=theta delta with theta<1/B_c force the plus tuple to be exact.

**Boundary.** This is not a defect-contraction iteration: rephasing
leaves kappa unchanged. It does not justify finite-order normalization
while preserving the scalar gap or exactification of approximately
invariant spectral sectors.

DERIVATION
wave2-ghb7-phase-normalization-proof
