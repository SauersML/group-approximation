---
rg: 2
id: amenable-extensions-of-uqs-groups-proof
kind: route
title: Transplant to the kernel over a Følner set, store the decoder boundary, and charge it to the tiles' deficit
target: amenable-extensions-of-uqs-groups-are-surjunctive
requires: []
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
  - research/artifacts/w3-vf-positive-verification-2026-09-12.md
---

Theorem B, Proposition 3.1 and Corollary 3.2, Section 3 of the artifact.

1. **Transplant.** For finite `F <= G/N` the encoder restricted to the cosets in `F` is an automaton over `N`
   (Lemma 2.1). Storing the configuration on `F^+ \ F^-` beside it gives an injective automaton over `N`.
2. **Tiles.** A Garden of Eden pattern of the image gives `n >= |F'| / |Wbar Wbar^-1|` disjoint tiles in `F`. On each
   tile the image avoids a transported pattern on `|W|` sites at every `N`-offset.
3. **Bookkeeping.** The full track of the target exceeds the source's leftover track by exactly `|F \ F^-|` symbols.
4. **Charge.**
   - Right Følner sets make `|F \ F^-|` a small fraction of the number of tiles, contradicting UQS.
   - Over a two-ended quotient `|F \ F^-|` stays bounded, contradicting AQS.
5. **Heredity.** Extend coset by coset for subgroups, keeping the constants. Restrict to a coset for directed unions.
   That step needs one UQS constant function, or one AQS threshold function, shared by all stages, because a map
   living at stage `k` contradicts only that stage's constant.
6. **Ascending HNN extensions.** Their kernel onto `Z` is a directed union of isomorphic copies of `N`, so the stages
   share `N`'s threshold.

**Verification.** `w3-vf-positive` passed this route (Sections 19.1–19.3 of `research/artifacts/w3-vf-positive-verification-2026-09-12.md`). Scope note: heredity to directed unions needs one UQS constant, or one AQS threshold, shared by all stages. The isomorphic stages of Corollary 3.2 have that.
