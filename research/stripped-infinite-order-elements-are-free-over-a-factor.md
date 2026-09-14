---
rg: 2
id: stripped-infinite-order-elements-are-free-over-a-factor
kind: claim
title: An element of A*B outside A generates a free product with A exactly when its core, stripped of A-syllables at both ends, has infinite order
distinct_from:
  klyachko-kl-holds-when-all-coefficients-have-infinite-order: that imports Klyachko's simple fact, which needs every syllable of u to have infinite order; this needs only the stripped core to have infinite order, and it is sharp.
artifacts:
  - research/artifacts/hl-kl-two-level-words-2026-09-14.md
---

Let `A`, `B` be groups and `u in (A * B) \ A`. Write the normal form of `u` as

    u = x · u' · x',        x, x' in A,

where `u'` is nontrivial and its normal form begins and ends with a syllable
in `B` (strip at most one `A`-syllable from each end). Call `u'` the *core*.

1. **Free-factor criterion.** The homomorphism `A * <z>_inf -> A * B` that is the
   identity on `A` and sends `z -> u` is injective if and only if `u'` has
   infinite order. In that case `gp(A, u) = A * <u>_inf`.
2. **Finite-order criterion.** In any free product `*_(j in J) G_j`, let
   `gamma = gamma_1 ... gamma_L` be a reduced word whose first and last
   syllables lie in the same factor. Then `gamma` has finite order if and only
   if `L` is odd, `gamma_(L+1-r) = gamma_r^(-1)` in the same factor for
   `1 <= r <= (L-1)/2`, and the middle syllable `gamma_((L+1)/2)` has finite
   order in its factor. A reduced word of length at least two whose first and
   last syllables lie in different factors always has infinite order.

**Consequence.** Klyachko's simple fact ("if `u in (A*B) \ A` and each factor of
`u` has infinite order, then `gp(A,u) = A * <u>_inf`") holds under the weaker
hypothesis that the core has infinite order. Finite-order syllables are
harmless at the ends of `u`, and anywhere except as the middle of an inverse
palindrome.

**Sharpness.** If `u'` has finite order `k`, then `(x^(-1) z x'^(-1))^k` is a
nontrivial element of `A * <z>` mapping to `u'^k = 1`.

**ESTABLISHED** through `stripped-infinite-order-free-factor-proof`.
Elementary, using normal forms in free products. Model-tested in the artifact.
Not independently reviewed; no novelty claimed.
