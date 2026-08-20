---
rg: 2
id: fault-tolerant-clifford-tape-route
kind: route
title: Jointly encode a self-similar Clifford tape so localized sacrifice cannot dilute the mark
target: same-model-supercritical-clifford-trigger
requires:
  - slofstra-subexponential-hyperlinear-profile
  - robust-clifford-capacity-bound
  - bgv-adversarial-fault-tolerance
  - clifford-hs-defect-becomes-adversarial-site-noise
  - clifford-tape-escapes-sofic-halo-permanence
  - conjugacy-compressed-dimension-trigger
---

Use Slofstra's shift/HNN addressing to expose a growing family of Clifford
sites from finitely many generators.  On the separated marked carrier, apply
the site-noise bridge and jointly encode all addressed sites by the
subsystem-product fault-tolerance scheme.  Because the logical data is one
high-distance block, an approximator cannot erase one tiny site or one tiny
logical block and dilute that erasure in normalized dimension.

The self-similar trigger must choose, inside the same candidate `d`-dimensional
model, a code instance whose required protected Clifford capacity exceeds
`d`.  Slofstra's robust capacity lemma then supplies the terminal
contradiction.  A sequence of larger external models is not enough.

This route is conditional on the site-noise bridge.  The cited fault-tolerance
theorem alone starts with an external tensor-product architecture and therefore
does not establish this Cairn target.  It must also pass the Alekseev--Bradford
falsification test: a functorial coded halo moved by a sofic action is still
hyperlinear.
