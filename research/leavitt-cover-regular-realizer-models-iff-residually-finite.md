---
rg: 2
id: leavitt-cover-regular-realizer-models-iff-residually-finite
kind: claim
title: The hyperbolic Leavitt cover has a realized sofic approximation with regular kernel blocks exactly when it is residually finite
distinct_from:
  leavitt-cover-finite-quotients-split-over-the-kernel: that determines the finite quotients of the cover and says residual finiteness means the canonical inner realizers separate G; this shows the same condition is exactly the existence of a sofic approximation whose kernel blocks are Cayley graphs of finite groups and on which every element has blockwise inner realizers of any length.
  kernel-block-realizers-need-no-centralizer-factor: that removes centralizer factors from realizers; this uses it to turn realized approximations with regular blocks into finite quotients.
  inner-realizers-are-at-least-half-the-sofic-radius: that bounds realizer length by the sofic radius; this identifies which realized approximations with regular blocks exist.
  bounded-blockwise-inner-realizers-fail-off-kernel: that excludes realizers of bounded length; this identifies the regular-block part of the unbounded case with residual finiteness.
---

**ESTABLISHED.** Let `G` be the hyperbolic Kazhdan cover
`1 -> N -> G -> R^x -> 1` of `hyperbolic-kazhdan-cover-of-leavitt-unit-group`,
`R = L_(F_2)(1,2)`. Use the notation of
`kernel-block-realizers-need-no-centralizer-factor`. Call a block `B`
**regular** if `Pi_B` acts regularly on `B`, i.e. `B` with its edited generators
is the Cayley graph of the finite group `Pi_B`. The following are equivalent.

1. `G` is residually finite.
2. `G` has a sofic approximation with a block decomposition of `sigma_n|N` and a
   `delta > 0` such that, along `U`, the regular blocks on which every generator
   of `G` is realized have total mass at least `delta |X_n|`. Here realized means
   agreement off `o(|X_n|)` points, with words of any length and block
   centralizer factors allowed.

**Moreover.**
- In 2, off `o(|X_n|)` of that mass the realizers are exact homomorphisms
  `r_B : G -> Pi_B` with `r_B(s) = s_B` for `s in S`. Their images are finite
  quotients `N/L` as in `leavitt-cover-finite-quotients-split-over-the-kernel`.
- In 1, the models are the finite quotients themselves, each a single block.

Derivation: `regular-realizer-models-residual-finiteness-proof`.

## What this says about the unbounded case of the realizer hinge

- In a realized approximation every element acts through the kernel's block
  groups (`kernel-block-realizers-need-no-centralizer-factor`), by words at least
  half as long as the sofic radius
  (`inner-realizers-are-at-least-half-the-sofic-radius`).
- On regular blocks, ruling out realized approximations is exactly proving that
  `G` is not residually finite. If `G` is residually finite, the finite-quotient
  models exist. They are genuine actions of `G`: they preserve the kernel block
  exactly and realize every element exactly, so every exact transport statement
  about genuine actions holds in them. An argument that reads only realizer
  structure and exact transport on regular blocks cannot reach
  `relative-normalization-modulo-kazhdan-kernel` without proving that this
  hyperbolic group is not residually finite (compare
  `non-residually-finite-hyperbolic-group`).
- Off regular blocks there is no constraint:
  `kernel-block-realizers-exist-after-small-re-edit` re-edits every sofic
  approximation of the cover into realized form, with alternating block groups.
  So the realized regime is populated iff the cover is sofic, and it is populated
  with regular blocks iff the cover is residually finite.
- In a realized injective model the relative defect `d` of the cover lies in `Pi`
  but not in `sigma(N)`. Realizers place `sigma(d)` in the block closure of
  `sigma(N)`, not in `sigma(N)`.

**Scope.** No property (T) of `G` is used: only Kun's blocks for `N`, finite
presentability of the hyperbolic group `G`, and the algebra of the quotient. It
proves no nonsoficity, and nothing about residual finiteness of `G` either way.
