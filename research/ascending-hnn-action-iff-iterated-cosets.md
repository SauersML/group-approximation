---
rg: 2
id: ascending-hnn-action-iff-iterated-cosets
kind: claim
title: Ascending-HNN coset soficity is exactly soficity of all iterated base coset actions
distinct_from:
  uas-base-gives-sofic-hnn-coset-action: That is one sufficient hypothesis on the base; this is an iff criterion with no UAS, LERA, LERF, finite-index, or residual-finiteness assumption.
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - GroupApproximation/Sofic/AscendingHNNSoficDescent.lean
  - GroupApproximation/Sofic/SoficActionCyclicExtension.lean
---

Let `Gamma` be countable, let `alpha : Gamma -> Gamma` be injective, let
`V = <Gamma,t | t gamma t^-1 = alpha(gamma)>` be the ascending HNN/vertical
model, and let `X = V/Gamma`.  Then

`V ↷ X` is a sofic action **if and only if**, for every `m >= 1`, the
transitive action

`Gamma ↷ Gamma / alpha^m(Gamma)`

is sofic.  Equivalently one may replace `V` by the telescope kernel
`N = union_m t^-m Gamma t^m` on the left.

The necessity identifies `Gamma/alpha^m(Gamma)` with the `Gamma`-orbit of the
site `t^m Gamma`.  For sufficiency, any finite action window for `N` is
contained in one telescope level; after conjugating that level back to the
base, every orbit meeting the finite test set has stabilizer conjugate to some
`alpha^m(Gamma)`.  The finite union of those orbit models gives the local
`N`-model, and the already-formalized cyclic-extension theorem adjoins the
stable-letter direction.

Full proof and the exact finitary window bookkeeping are in the artifact.
