---
rg: 2
id: a5-free-product-has-simple-arithmetic-shell-envelope
kind: claim
title: A bijective-base enumeration gives A5 free product A5 a decidable simple arithmetic shell envelope
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
---

Let P=A_5*A_5 and assign digits 1,...,59 to the nonidentity
elements in each factor, using the same fixed ordering. For a
nonempty reduced word with alternating factor types, first type
epsilon in {0,1}, and digits d_1,...,d_l, define

    q=sum_(j=1)^l d_j*59^(j-1),
    nu(word)=2*q-1+epsilon,
    nu(1)=0.

This is a computable bijection P->N. Its regular generator
permutations, and hence their even-shell copies, have effective
positive affine formulas on residue classes with finite exceptions.
The associated E_nu is finitely generated, simple, has decidable
word problem, and contains P faithfully.

Its specified Cantor action is not a subgroup of the rational
homeomorphism group. Each nonidentity factor element gives a
nonrational shell map in this enumeration. Whether this particular
E_nu is finitely presented remains OPEN; no such presentation
is supplied by the arithmetic algorithm.
