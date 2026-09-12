---
rg: 2
id: jacobson-shift-active-block-compactness-proof
kind: route
title: Retain all shifted heads in one active block and take a bounded-dimensional limit
target: jacobson-shift-block-permutation-models-have-a-gap
requires:
  - jacobson-shift-exact-representations-kill-head
  - jacobson-shift-gap-characterizes-mark-collapse
artifacts:
  - research/artifacts/jacobson-shift-exact-collapse-and-monomial-gap-2026-09-08.md
---

Different block permutations are separated by norm at least `sqrt(2)`.
Thus a hypothetical sequence of admissible block-permuting models
with vanishing mixed errors gives exact finite permutation quotients.
These kill the head by the first prerequisite, and kill `K` because
its elementary transvections are conjugates of the head root.

Each conjugate `T^i rho_B(K) T^-i` preserves every block. Exact
intertwining on `F` identifies the two adjacent heads inside it;
conjugacy there keeps all shifted head roots nonidentity on one chosen
marked block. Pad that block trivially to dimension `m`.

For `N=floor(m/2)+1`, finite-dimensional compactness gives limiting
representations of its first `N` head groups. Every fixed distant
commutator is a finite consequence of the presentation, so its error
tends to zero and the limits commute. Their marked involutions retain
norm distance two. The tensor dimension bound would require `m>=2N`,
a contradiction. Section 6 of the artifact supplies the full argument.
