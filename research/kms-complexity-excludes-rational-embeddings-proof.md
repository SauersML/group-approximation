---
rg: 2
id: kms-complexity-excludes-rational-embeddings-proof
kind: route
title: Transfer the rational word-problem bound across an embedding and contradict recursive time hardness
target: decidable-fp-groups-need-not-embed-in-rational-group
requires:
  - rational-homeomorphism-subgroups-have-exponential-wp
artifacts:
  - research/artifacts/boone-higman-finite-state-and-shell-germ-limits-2026-09-08.md
---

[Kharlampovich--Myasnikov--Sapir, Algorithmically complex residually
finite groups](https://link.springer.com/article/10.1007/s13373-017-0103-z),
Theorem 4.21, supplies for every recursive membership problem X a
finitely presented residually finite group G, solvable of class 3,
whose word problem is at least as hard as X. Their Definition 2.2(a)
specifies the needed quantitative meaning: a time-T algorithm for
the harder problem supplies an algorithm for the other problem in
time bounded by C*T(C*n)+C*n+C for some constant C. This is a
word-problem hardness result; a large Dehn function alone would not
give the conclusion used here.

Choose a recursive membership problem X with no deterministic
2^O(n)-time algorithm. Such a recursive problem follows directly by
diagonalizing over pairs (machine, positive integer c), with the
machine clocked at 2^(c*n+c) steps. At the encoding assigned to a
pair, simulate its clocked answer and return the opposite answer.
Every simulation is finite, so this defines a recursive problem;
any decision procedure satisfying a single-exponential bound has
a sufficiently large clock in the list and disagrees at its own
assigned input. One may do this with unary encodings as well, if
natural numbers are represented in unary.

Apply the cited theorem to X. The resulting G has decidable word
problem, either by the theorem's reduction to recursive X or by
finite presentation and residual finiteness. It has no 2^O(n)-time
word-problem algorithm: the comparison C*T(C*n)+C*n+C preserves
single-exponential bounds and would give the excluded algorithm
for X.

An embedding of G into a rational homeomorphism group would, by the
required claim, give just such a word-problem algorithm. This is a
contradiction. The alphabet size and sizes of the image transducers
may depend arbitrarily on G; they are still fixed constants after
an embedding is chosen. No effectiveness of the embedding is assumed.

This combines an imported hardness theorem with the explicit cascade
bound. No novelty of the resulting nonembedding observation is claimed,
and neither route is a Lean certificate.
