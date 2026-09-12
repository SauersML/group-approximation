---
rg: 2
id: clean-shear-dilation-equivalence-proof
kind: route
title: Run the Bennett circuit with formal representatives, and in the other direction read the decoder off the reversed circuit
target: formalizable-left-inverse-iff-clean-shear-dilation
requires: []
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Section 2 of the artifact.
- (a) ⇒ (b). With formal representatives, `W = P o S o T` is a word of commuting track shears and a
  swap, and `W~(X,0) = (tau~(X), X + sigma~(tau~(X))) = (tau~(X), 0)` formally.
- (b) ⇒ (a). Put `sigma = pi_1 o W^-1 o iota_0`, with the reversed word as representative.
  - Functionally, `W(x,0) = (tau(x),0)` gives `sigma o tau = id`.
  - Formally, `sigma~(tau~(X)) = pi_1 W~'(W~(X,0)) = X`.
