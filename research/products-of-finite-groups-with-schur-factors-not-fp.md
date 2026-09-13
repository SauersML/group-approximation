---
rg: 2
id: products-of-finite-groups-with-schur-factors-not-fp
kind: claim
title: A subgroup of a product of finite groups containing their direct sum is not finitely presented when infinitely many factors have nonzero H_2
distinct_from:
  fp2-over-q-descends-along-locally-finite-kernels: that passes rational FP_2 from a group to its quotient by a locally finite normal subgroup; this is an integral H_2 obstruction on the group itself, for groups containing the whole restricted product.
  cycle-transposition-lef-group-is-not-finitely-presented: that settles one two-generated group through Houghton's H_2 and rational FP_2; this excludes every group containing a restricted product of finite groups with infinitely many nonzero Schur multipliers.
---

**Statement.** Let `(S_n)_(n >= 1)` be finite groups, and let `G` be a subgroup of
`prod_n S_n` that contains the restricted product `(+)_n S_n`. If
`H_2(S_n; Z) != 0` for infinitely many `n`, then `H_2(G; Z)` is not finitely
generated. In particular `G` is not finitely presented.

The proof is `products-with-schur-factors-not-fp-proof`. It is elementary, and
no novelty is claimed.

**Scope.**
- Finite generation of `G` is not assumed.
- The hypothesis needs every coordinate copy of `S_n` inside `G`.
- The obstruction says nothing when all but finitely many `S_n` are perfect with
  trivial Schur multiplier.
