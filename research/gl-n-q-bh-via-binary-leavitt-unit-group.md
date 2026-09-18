---
rg: 2
id: gl-n-q-bh-via-binary-leavitt-unit-group
kind: route
title: An embedding of GL_n(Q) in the finitely presented simple binary Leavitt unit group answers the root
target: gl-n-q-embeds-in-fp-simple-group
requires:
  - gl-n-q-embeds-in-binary-leavitt-unit-group
  - leavitt-unit-group-finitely-presented
  - binary-leavitt-unit-group-is-simple
---

Let `U = L_(F_2)(1,2)^x`. By `leavitt-unit-group-finitely-presented` it is finitely presented. That is a
literature import (Khanh arXiv:2609.08428v1, Theorem 6.1) whose proof has not been reviewed in this graph. By
`binary-leavitt-unit-group-is-simple` it is simple. So an injective homomorphism `GL_n(Q) -> U`
(`gl-n-q-embeds-in-binary-leavitt-unit-group`) is an embedding of `GL_n(Q)` in a finitely presented simple
group, for every `n >= 2`. ∎

The route is conditional on its first premise. `rationals-do-not-embed-in-binary-leavitt-unit-group` would
invalidate it.
