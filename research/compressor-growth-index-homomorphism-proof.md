---
rg: 2
id: compressor-growth-index-homomorphism-proof
kind: route
title: Combine automorphism invariance of the index with tower multiplicativity
target: compressor-growth-index-homomorphism
requires: []
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

`Ad pi(s_1 s_2)=Ad pi(s_1) Ad pi(s_2)` turns the two one-sided inclusions
into a three-term tower `N<=Ad pi(s_1)(N)<=Ad pi(s_1s_2)(N)`.  The top index
equals `lambda(s_2)` because a trace-preserving automorphism preserves the
Pimsner--Popa index, and the bottom index is `lambda(s_1)`.  Submultiplicativity
of the index follows from applying the Pimsner--Popa inequality twice, and
multiplicativity in the finite case is the standard tower theorem.  Index one
characterizes equality of the inclusion, and normalizers give `N_s=N`.  The
tower and infinite-index corollaries are then immediate.  Complete argument
in the cited note, Theorem 4 and Corollary 5.
