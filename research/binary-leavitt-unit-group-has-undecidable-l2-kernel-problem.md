---
rg: 2
id: binary-leavitt-unit-group-has-undecidable-l2-kernel-problem
kind: claim
title: Over the integral group ring of the binary Leavitt unit group, triviality of l2-kernels and being a zero-divisor are undecidable
distinct_from:
  binary-leavitt-unit-word-problem-decidable: that is decidability of the word problem of the same group; this shows that two spectral and ring-theoretic questions over its group ring stay undecidable although the word problem is decidable.
  binary-leavitt-unit-group-has-irrational-l2-betti-numbers: that is irrationality of kernel dimensions; this is undecidability of whether they vanish.
---

**ESTABLISHED (proved on paper, unreviewed).** Let `G = L_(F_2)(1,2)^x`, given by a finite
generating set.
1. No algorithm decides, given `M in M_k(Z[G])`, whether `ker M = {0}` on `ℓ²(G)^k`, or
   equivalently whether `dim_vN ker M = 0`.
2. No algorithm decides whether a given matrix over `Z[G]` is a zero-divisor.

Since `G` is finitely presented, (1) says that no algorithm decides vanishing of a given L²-Betti
number of a finite CW complex with fundamental group `G`. This uses Eckmann's realization of any
matrix as a combinatorial Laplacian, as in Grabowski's introduction. The same holds for every group
containing `V`, including `(B ⊗ L)^x` for simple `B`.

**Contrast.**
- The word problem of `G` is decidable (`binary-leavitt-unit-word-problem-decidable`).
- Grabowski's conditional algorithm (a decidable word problem plus bounded finite subgroups) does not
  apply, because `G` contains every finite group.
- Every kernel dimension over `G` is right-computable (`decidable-groups-have-right-computable-l2-betti-numbers`).

Route: `binary-leavitt-unit-undecidable-l2-kernel-proof`.
