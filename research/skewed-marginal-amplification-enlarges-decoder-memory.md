---
rg: 2
id: skewed-marginal-amplification-enlarges-decoder-memory
kind: claim
title: Skewed-marginal amplifications of symbol-complete three-point-decoder strict automata have no three-point left inverse
distinct_from:
  strict-automata-give-injective-ca-with-skewed-site-marginals: that builds the amplified injective automaton and bounds its single-site entropy; this asks whether every left inverse of that automaton needs more than three points, which decides whether three-point domination can feed the three-point-decoder surjectivity claim.
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
  - research/artifacts/gk-vf-positive-b-verification-2026-09-12.md
---

**OPEN.** Let `tau` be a strict automaton over `G` with a left inverse of memory `N_tau = {e, s, t}`, `<s, t>`
nonamenable. Suppose every pattern missing from the image of `tau` needs at least two sites, so every symbol occurs in
the image. Let `kappa` on `(A^(k+1))^G` be an injective automaton given by the construction of
`strict-automata-give-injective-ca-with-skewed-site-marginals`. Then no left inverse of `kappa` has three-point memory.

**If true**, the reduction proposed on `three-point-decoder-memory-injective-ca-are-surjective` (amplify, then dominate
the transport for three-point decoders) cannot run for this class. **If false**, three-point domination would give
surjectivity for these strict pairs too.

**Restated at the third landing** (after w4-vf-positive-b §5). The earlier statement covered every strict `tau`. It
fails whenever the image of `tau` avoids a symbol: there `Omega = {e}`, the constructed left inverse has memory
`N_tau`, and the reduction runs (artifact 3.1). So the claim is now stated only for strict `tau` whose missing
patterns all need at least two sites.

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
- **Where the claim as stated fails** (w4-vf-positive-b, Section 5.4 of
  `research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`).
  - *The constructed left inverse.* Its memory is exactly `N_tau Omega^-1 (Omega Omega^-1 ∪ Omega)`.
  - *The exception.* Suppose the image of `tau` avoids one symbol at a site, so `Omega = {e}`. Then that memory is `N_tau`,
    three points, and the site law is still skewed. So the claim fails for every such `tau`.
  - *What this means for a proof.* A proof of the claim as stated would show that no strict automaton with a three-point left
    inverse avoids a symbol. For such automata the proposed reduction runs.
  - *The remaining case.* When `|Omega| >= 2` and `<s, t>` is nonamenable, the constructed memory has more than three points,
    by a coset count.
  - *Recommendation.* Restate the claim for strict `tau` whose missing patterns all need at least two sites.
