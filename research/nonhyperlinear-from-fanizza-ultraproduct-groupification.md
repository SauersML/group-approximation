---
rg: 2
id: nonhyperlinear-from-fanizza-ultraproduct-groupification
kind: route
title: Feed qualitative Fanizza mark death into the threshold-free reverse-Kleene diagonal
target: non-hyperlinear-group
requires:
  - fanizza-native-signal-ultraproduct-groupification
  - threshold-free-reverse-kleene-higman-diagonal
---

The groupifier supplies `(TFK1)` because its HALT representation detects
`d_m`, so the word is algebraically nontrivial. Its NONHALT clause is exactly
`(TFK2)`. Apply the proof-enumeration fixed point from
`threshold-free-reverse-kleene-higman-diagonal` to obtain a finitely generated
recursively presented group with a nontrivial hyperlinear-radical element, then
apply effective Higman embedding. Hyperlinearity passes to subgroups, so the
finitely presented overgroup is non-hyperlinear.
