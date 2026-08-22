---
rg: 2
id: effective-twisted-factor-existence-is-equivalent-to-fp-nonhyperlinearity
kind: claim
title: The effective bad-twist gate is exactly finitely presented nonhyperlinearity
distinct_from:
  effective-nonce-twisted-factor-exists: that is the open existential statement using a finite-rank free quotient with recursively enumerable kernel; this theorem identifies it exactly with the desired finitely presented witness rather than treating it as a weaker compiler input.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that permits arbitrary countable groups and proves finite generation is free; the present theorem identifies recursively enumerable kernel as precisely the extra Higman-level content.
  recursive-twisted-factor-higman-compiler: that proves only the forward compilation from one effective twist; this includes the trivial-cocycle converse and hence an equivalence.
---

The following are equivalent.

1. There are a finite-rank free group `F`, a recursively enumerable normally
   generated subgroup `N normal F`, and a scalar multiplier `omega` on `F/N`
   such that `L_omega(F/N)` is not Connes embeddable.
2. There is a finitely generated recursively presented nonhyperlinear group.
3. There is a finitely presented nonhyperlinear group.

Thus `effective-nonce-twisted-factor-exists` is already an exact
reformulation of finitely presented nonhyperlinearity.  The multiplier need
not itself be computable for the forward implication: the recursive group
produced by the relation-centralizing compiler depends only on the r.e.
kernel `N`.  In the converse direction the multiplier is the computable
trivial cocycle.

