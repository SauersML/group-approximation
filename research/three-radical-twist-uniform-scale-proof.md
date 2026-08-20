---
rg: 2
id: three-radical-twist-uniform-scale-proof
kind: route
title: Apply Clifford theory to the three translations of the four hot radical characters
target: three-radical-twist-crossed-products-have-uniform-scale
requires:
  - every-predicate-has-s3-equivariant-raw-radical-drop
---

Multiplying generator `g_v` by the central involution `J^(ell(v))` preserves
all squares and commutators, and linearity of `ell` preserves multiplication;
this proves `(RTC2)`.  Twisting an irreducible marked `K_f` representation by
`tau_i` translates its radical character by `ell_i`.

If the radical is zero, there is one `K_f` simple.  The twist fixes its
equivalence class and acts by an inner automorphism of its full matrix
algebra.  The `C_2` crossed product is therefore two copies of that matrix
algebra.

If the radical is two-dimensional, there are four simples of dimension
`D_0/2`.  Translation by a nonzero vector has two free two-point orbits.
Clifford theory identifies the crossed product over each orbit with
`M_(2(D_0/2))=M_(D_0)`.  This proves `(RTC4)`.  The natural `S3` action on the
radical is transitive on its three nonzero dual vectors, proving conjugacy of
the charts.  The artifact exhausts the orbit and dimension ledger for every
predicate of arity at most three.
