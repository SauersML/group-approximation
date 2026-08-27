---
rg: 2
id: mf-safe-asymmetric-hnn-via-relative-profinite-compatibility
kind: route
title: Keep the rope edge and prove it MF from finite quotients of the witness
target: mf-safe-asymmetric-hnn-replacement
requires:
  - twisted-rope-edge-is-mf-under-relative-profinite-compatibility
  - benign-witness-finite-quotients-refine-the-fold
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
---

Do not replace the asymmetric identification.  Use the bidirectional
finitely generated bridge so that the `INF`-branch quotient `Q = F/N` is
residually finite, verify the relative profinite compatibility of the benign
witness on `S = F *_N F`, and apply the twisted-edge theorem with `Gamma`
the (already MF-safe) witness.  The output group `R` is then MF on the `INF`
branch, and Britton's lemma keeps `E` embedded on the `FIN` branch.
