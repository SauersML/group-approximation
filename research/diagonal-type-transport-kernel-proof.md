---
rg: 2
id: diagonal-type-transport-kernel-proof
kind: route
title: Jointly diagonal transported cuts annihilate every normalizer test
target: normalizer-phase-tests-leave-diagonal-type-transport
requires:
  - fourier-normalizer-words-control-block-gram-leakage
---

The margin identities in `(NPT1)` follow by summing over either partition
and using `P^*P=PP^*=1`.  If every `PF_jP^*` commutes with every `E_i`, then
all off-diagonal blocks `(NPT2)` vanish.  The two-partition version of the
Fourier calculation, or the same block multiplication used in `(FNG1)`,
therefore makes every normalizer commutator zero.

Choose orthogonal target atoms of the required ranks and map each `F_j`
unitarily onto an arbitrary union of them.  This realizes any integral
transport table with the prescribed margins while retaining zero normalizer
energy.  Choosing the image of `S` inside `I-C` gives `(NPT3)`.
