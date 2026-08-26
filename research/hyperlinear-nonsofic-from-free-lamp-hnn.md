---
rg: 2
id: hyperlinear-nonsofic-from-free-lamp-hnn
kind: route
title: A hyperlinear free-lamp HNN group contains the nonsofic Kun--Thom double
target: hyperlinear-nonsofic-group
requires:
  - kt-free-lamp-hnn-group-is-hyperlinear
  - kt-pair-group-double-is-nonsofic
---

In `H = G *_Gamma (Gamma x <s>)`, an element `s h s^(-1)` with `h in G - Gamma`
is a Britton-reduced word and lies outside the base `G`, so
`G cap sGs^(-1) = Gamma`; the normal-form theorem then identifies
`<G, sGs^(-1)>` with the amalgam `G *_Gamma G = D`.  Hyperlinearity passes to
subgroups, so `H` hyperlinear gives `D` hyperlinear, and `D` is nonsofic by
`kt-pair-group-double-is-nonsofic`.
