---
rg: 2
id: skewed-marginal-amplification-enlarges-decoder-memory
kind: claim
title: The skewed-marginal amplification of a strict automaton has a strictly larger left-inverse memory
distinct_from:
  strict-automata-give-injective-ca-with-skewed-site-marginals: that builds the amplified injective automaton and bounds its single-site entropy; this records that its left-inverse memory strictly contains the original decoder memory, so three-point domination does not reduce the three-point-decoder surjectivity claim.
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
---

**ESTABLISHED** by `skewed-marginal-amplification-enlarges-decoder-memory-proof`.

Let `tau` be a strict automaton with left-inverse memory `N_tau`, image missing a pattern on the window `Omega`, and
let `kappa` on `(A^(k+1))^G` be the injective automaton of
`strict-automata-give-injective-ca-with-skewed-site-marginals`. Every left inverse of `kappa` has memory containing
`N_tau ∪ W_anchor ∪ W_block`, where `W_anchor` is the window that locates the self-separating anchor pattern on
`Omega Omega^{-1}` in track `0`, and `W_block` is the anchored-block window of the greedy recoding. Generically this
is strictly larger than `N_tau`, and larger than any three-point memory.

**Consequence.** The reduction proposed for `three-point-decoder-memory-injective-ca-are-surjective` — amplify `tau`,
then dominate the transport of the amplified automaton — targets `kappa`, whose memory is `N_tau ∪ W_anchor ∪ W_block`,
not three points. So proving domination for three-point-decoder automata does not establish that claim by
amplification. The claim is either (i) the `h_fin` statement that three-point-decoder injective automata have full
single-site entropy, a special case of `injective-ca-images-have-full-single-site-entropy`, or (ii) a surjectivity
statement whose transport route runs through the enlarged-memory `kappa`, where
`transport-identity-gives-reciprocal-memory-entropy-bound` gives only the reciprocal bound.

## Attempts
- No way is known to amplify a strict `tau` into an injective automaton whose left inverse keeps three points while
  skewing a single-site law; the anchor track and the block recoding are both needed to invert (see the proof route),
  and each adds decoder sites.
