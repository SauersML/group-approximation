---
rg: 2
id: hard-self-similar-groups-from-fp-rf-embedding
kind: route
title: Put the Kharlampovich--Myasnikov--Sapir groups inside finitely presented self-similar groups
target: fp-self-similar-groups-with-arbitrarily-hard-word-problem
requires:
  - every-fp-rf-group-embeds-in-fp-self-similar-group
  - kms-arbitrarily-hard-fp-rf-groups
---

Fix a recursive `T`, and put `T+(m) = m + max_(k<=m) T(k)`.

1. **A hard input.** Diagonalization, as in step 1 of
   `uniform-wp-bound-excludes-bh-universal-targets`, gives a recursive set `X`
   outside `F(T+)`.
2. **A hard group.** `kms-arbitrarily-hard-fp-rf-groups`, condition `(KMS1)`,
   turns `X` into a finitely presented residually finite group `G_X` whose
   word problem is outside `F(T+)`.
3. **A self-similar overgroup.** `every-fp-rf-group-embeds-in-fp-self-similar-group`
   gives a finitely presented self-similar `H` with `G_X <= H`.
4. **Transfer.** A word-problem algorithm for `H` within
   `C*T(C*l) + C*l + C` would, by the length-linear substitution of
   `complexity-bounded-host-classes-are-not-universal-proof`, put `WP(G_X)` in
   `F(T+)`, a contradiction.

So `H` beats `T`. `∎`

This route only records that the target is a special case of the embedding
claim. The embedding claim is much stronger than what the target needs.
