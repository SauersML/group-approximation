---
rg: 2
id: every-group-positive-rokhlin-gives-tester-host-case
kind: route
title: Specialize the universal positive Rokhlin entropy statement to the Gottschalk tester host
target: tester-host-has-positive-rokhlin-entropy-action
requires:
  - every-group-has-positive-rokhlin-entropy-action
---

The tester host of `tester-host-has-positive-rokhlin-entropy-action` is a
countably infinite group. So the universal statement
`every-group-has-positive-rokhlin-entropy-action`, applied to that group, gives
a free ergodic p.m.p. action of it with positive Rokhlin entropy.

This is a pure specialization. Composed with
`positive-rokhlin-entropy-on-one-host-proves-gottschalk`, it shows that the
universal Rokhlin statement implies Gottschalk's conjecture for every group.
