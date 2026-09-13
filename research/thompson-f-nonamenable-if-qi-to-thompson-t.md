---
rg: 2
id: thompson-f-nonamenable-if-qi-to-thompson-t
kind: route
title: "If Thompson's group F is quasi-isometric to T, then F is not amenable"
target: thompson-f-is-not-amenable
requires:
  - thompson-f-is-quasi-isometric-to-thompson-t
  - amenability-is-a-quasi-isometry-invariant
  - thompson-t-is-not-amenable
---

Suppose F is quasi-isometric to T. If F were amenable, then by
`amenability-is-a-quasi-isometry-invariant`, applied with `H = F` and `G = T`, T
would be amenable, contradicting `thompson-t-is-not-amenable`. So F is not
amenable. This is the contrapositive packaging of
`thompson-f-not-qi-to-t-if-f-is-amenable`: a yes-answer to Zaremsky Problem 2.4(c)
settles Zaremsky Problem 2.1 negatively.
