---
rg: 2
id: gl-n-q-root-from-countable-decidable-bh
kind: route
title: GL_n(Q) is a countable group with a solvable word problem
target: gl-n-q-embeds-in-fp-simple-group
requires: [countable-decidable-groups-embed-in-fp-simple-groups]
---

The survey, proof of Proposition 3.3(2), verbatim: for `GL_n(Q)` "it is easy to
enumerate a generating set ..., and the word problem is solvable by direct matrix
computations". Enumerate the matrices with rational entries and nonzero
determinant. A word in them is the identity iff its product, computed exactly
over `Q`, is the identity matrix. So `countable-decidable-groups-embed-in-fp-simple-groups`
embeds `GL_n(Q)` in a finitely presented simple group for every `n`. ∎
