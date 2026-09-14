---
rg: 2
id: skewed-marginal-amplification-enlarges-decoder-memory
kind: claim
title: Skewed-marginal amplifications of three-point-decoder strict automata have no three-point left inverse
distinct_from:
  strict-automata-give-injective-ca-with-skewed-site-marginals: that builds the amplified injective automaton and bounds its single-site entropy; this asks whether every left inverse of that automaton needs more than three points, which decides whether three-point domination can feed the three-point-decoder surjectivity claim.
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
---

**OPEN.** Let `tau` be a strict automaton over `G` with a left inverse of memory `N_tau = {e, s, t}`, and let `kappa` on
`(A^(k+1))^G` be an injective automaton given by the construction of
`strict-automata-give-injective-ca-with-skewed-site-marginals`. Then no left inverse of `kappa` has three-point memory.

**If true**, the reduction proposed on `three-point-decoder-memory-injective-ca-are-surjective` (amplify, then dominate
the transport for three-point decoders) cannot run as stated. **If false**, three-point domination would give
surjectivity for three-point-decoder strict pairs.

## Attempts
- **The constructed decoder reads more.** The left inverse built in the construction reads `N_tau ∪ W_anchor ∪ W_block`:
  the anchor-recognition window on track `0`, the recoded-block window, and the decoder of `tau` (artifact Section 3).
  That bounds one left inverse, not every left inverse. An earlier version landed this as ESTABLISHED on the grounds
  that "each step reads sites the others do not". That argument is about the procedure only, so it was withdrawn and
  its proof route deleted.
- **Proved lower bound.** Artifact Lemma 3.1: any left inverse of `kappa` with memory `N` restricts to a left inverse
  of `tau` with memory contained in `N`. Use a constant anchor-free track `0` and constant tracks `2..k`. This gives
  `|N| >= 3` when `tau` has no smaller left inverse, but no enlargement.
- **Where it dies.** A lower bound past three points needs an argument that every left inverse must read the whole
  recoded block, or the anchor window, and none is known in general.
