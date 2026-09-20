---
rg: 2
id: kazhdan-internality-from-blocks-and-exhaustion
kind: route
title: "Match at each fixed tolerance, then diagonalize expectations rather than spectral gaps"
target: kazhdan-commutants-are-internal
requires: [quotient-gap-expectations-have-coordinate-lifts, quotient-gap-gives-large-scalar-expanding-blocks, scalar-expanding-kazhdan-blocks-give-internality, internal-corners-exhaust-kazhdan-commutants]
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 6.7 and its assembly of §§3–6. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

Property (T) applied to conjugation on L^2(M) gives a quotient spectral gap. The coordinate-expectation prerequisite supplies one fixed lift of E_C on the whole operator unit ball.

For epsilon_k decreasing to zero apply the large-block theorem at fixed k. Repeating each generator twice does not change pi(H). The resulting retained projection p_k belongs to C, has complement trace <=epsilon_k, and the retained blocks have one positive gap c_k at this k. Restrict and normalize the corner trace; the matching prerequisite shows p_k C p_k is internal. The corner identities are literal because p_k commutes with pi(H). Exhaust by these internal corners using the last prerequisite. No passage assumes inf_k c_k>0.
