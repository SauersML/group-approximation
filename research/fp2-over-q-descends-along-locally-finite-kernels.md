---
rg: 2
id: fp2-over-q-descends-along-locally-finite-kernels
kind: claim
title: If a group is of type FP_2 over Q and L is a locally finite normal subgroup, then G/L is of type FP_2 over Q; in particular finitely presented groups descend this way
distinct_from:
  cycle-transposition-lef-group-is-not-finitely-presented: that is one application, to a block-diagonal residually finite group; this is the general descent lemma it uses.
  fp-rf-group-with-unbounded-prime-torsion: that asks for a finitely presented residually finite group with unbounded prime torsion; this is a necessary condition any block-diagonal candidate must pass.
---

**ESTABLISHED** by the elementary proof in
`fp2-over-q-descends-along-locally-finite-kernels-proof` (not independently
reviewed).

Let `G` be a group and `L` a locally finite normal subgroup of `G`.

1. For every left `Q[L]`-module `M`, write `M_L = M / I_L M`, where `I_L` is the
   augmentation ideal of `Q[L]`. Then `I_L M` is exactly the set of `m in M`
   with `e_F m = 0` for some finite subgroup `F <= L`, where
   `e_F = |F|^(-1) sum_(f in F) f`. The functor `M -> M_L` is exact.
2. If `G` is of type `FP_2` over `Q`, then `G/L` is of type `FP_2` over `Q`.
3. Every finitely presented group is of type `FP_2` over `Q`. So if `G` is
   finitely presented, `G/L` is of type `FP_2` over `Q`.

This is the rational form of the standard fact that locally finite groups are
invisible to rational homology. It is not claimed as new.

DERIVATION
fp2-over-q-descends-along-locally-finite-kernels-proof
