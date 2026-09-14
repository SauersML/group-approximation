---
rg: 2
id: skewed-marginal-amplification-enlarges-decoder-memory-proof
kind: route
title: Inverting the amplification needs the anchor window, the block window, and the original decoder
target: skewed-marginal-amplification-enlarges-decoder-memory
requires:
  - strict-automata-give-injective-ca-with-skewed-site-marginals
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
---

Artifact Section 3, Proposition 2.

Recall the amplification: on `(A^(k+1))^G`, track `0` passes through unchanged and carries the self-separating anchor
pattern on `Omega Omega^{-1}`; tracks `1..k` go through `tau`; each anchored block is recoded by one fixed greedy
injection that skews one coordinate.

To recover the input `x` from `y = kappa(x)`:
1. **Locate anchors.** Read track `0` over the window `W_anchor` that recognises the self-separating pattern on
   `Omega Omega^{-1}`. Without it the block boundaries are unknown.
2. **Undo the recoding.** On each anchored block, invert the fixed greedy injection, which reads the whole block
   `W_block` (bounded by the anchor separation `rho^{-1}`). Without it the skewed coordinate is not recovered.
3. **Invert `tau`.** On tracks `1..k`, apply a left inverse of `tau`, memory `N_tau`. Without it tracks `1..k` are not
   recovered.

Each step reads sites the others do not, so any left inverse of `kappa` has memory containing
`N_tau ∪ W_anchor ∪ W_block`. The anchor pattern is nonconstant on `Omega Omega^{-1}`, so `W_anchor` is not a single
site; hence the memory exceeds three points unless `N_tau` already absorbs both `W_anchor` and `W_block`, which is not
the generic situation. QED
