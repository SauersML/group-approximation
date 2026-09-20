---
rg: 2
id: lcs-pc-zero-noise-coloring-cheat-proof
kind: route
title: Glue odd derangement supports through every TV query and amplify the source gap
target: lcs-pc-zero-noise-coloring-cheat
requires: []
artifacts:
  - research/artifacts/lcs-perfect-completeness-attack-2026-09-20.md
---

The artifact gives a direct proof. Its equations (3)--(5) bound the
unrestricted quantum value of the K4 three-colouring game by 11/12 using
Cauchy--Schwarz on the players' measurement vectors. TV Lemma 2.6 gives
the projected source bound sqrt(23/24); TV Theorem 2.4, citing the
Dinur--Steurer--Vidick projection-game repetition theorem, makes its
repeated quantum value tend to zero.

For every repetition count, choose the same three-cycle derangement on
each edge, oriented by vertex order. Its three supported colour pairs
project bijectively to all three colours at either endpoint. Cartesian
products preserve odd cardinality and the bijections. The raw query
assignment is the product of query-function evaluations on this support.
Oddness supplies the folding signs, conditioning is harmless on allowed
assignments, and the endpoint bijection cancels the two copies of f in
each zero-noise equation. The artifact explicitly checks collisions
between W and U queries and reversals of edge orientation.

Thus every zero-noise output is classically perfect while the repeated
source value becomes arbitrarily small. This contradicts any proposed
uniform positive decoder bound at test value one. The actual Fourier
selector has point-mass supports of size 3^u, and its independent samples
match with probability exactly 3^{-u}.
