---
rg: 2
id: triangular-conjugate-bs-chains-are-sofic
kind: claim
title: Strictly triangular conjugate Baumslag-Solitar chains are sofic
distinct_from:
  magnus-staggered-chain-sofic: That asks for all staggered one-relator kernels; this proves the subclass whose conjugators are conjugates of nonzero powers of strictly later generators.
artifacts:
  - research/artifacts/triangular-bs-chain-proof-2026-09-07.md
---

Let `x_i`, `i in Z`, be generators. For every `i`, choose nonzero integers
`l_i,k_i,s_i`, an index `j_i>i`, and a finite word `U_i` using only
generators `x_j` with `j>i`. Set

    c_i = U_i^(-1) x_(j_i)^(s_i) U_i.

Then the group

    P = <x_i (i in Z) | c_i^(-1) x_i^(l_i) c_i = x_i^(k_i) (i in Z)>

is sofic. The same conclusion holds when only a subset of these relations
is imposed. No bound on the lengths of `U_i` or on `j_i-i` is required.

This is a theorem about abstract finite permutation approximability, with a
written proof using the standard amenable-edge permanence theorems. It has
not been formalized in Lean. It does not assert soficity for an arbitrary
free-edge Magnus amalgam.
