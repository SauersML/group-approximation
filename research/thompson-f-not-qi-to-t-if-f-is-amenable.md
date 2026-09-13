---
rg: 2
id: thompson-f-not-qi-to-t-if-f-is-amenable
kind: route
title: "If Thompson's group F is amenable, it is not quasi-isometric to T"
target: thompson-f-is-not-quasi-isometric-to-thompson-t
requires:
  - thompson-f-is-amenable
  - amenability-is-a-quasi-isometry-invariant
  - thompson-t-is-not-amenable
---

Suppose F is amenable and F is quasi-isometric to T. By
`amenability-is-a-quasi-isometry-invariant`, applied with `H = F` and `G = T`, T is
amenable, contradicting `thompson-t-is-not-amenable`. So F is not quasi-isometric
to T.
