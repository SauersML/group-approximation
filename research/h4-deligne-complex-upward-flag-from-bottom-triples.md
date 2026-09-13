---
rg: 2
id: h4-deligne-complex-upward-flag-from-bottom-triples
kind: route
title: Upward flagness of the H_4 Deligne complex from its bottom-triple condition and the H_3 theorem
target: h4-deligne-complex-upward-flag-toward-5-edge
requires:
  - spherical-path-upward-flagness-reduces-to-bottom-triples
  - h3-deligne-complex-upward-flag-toward-5-edge
  - h4-deligne-complex-bottom-triples-have-upper-bounds
---

Apply `spherical-path-upward-flagness-reduces-to-bottom-triples` to `Λ = s_1 s_2 s_3 s_4` of type
`H_4` with `m_{s_3 s_4} = 5`.

- Hypothesis (a) asks that `Δ_{Λ_{>1}}` be upward flag, where `Λ_{>1} = s_2 s_3 s_4` is `H_3` with
  `m_{s_3 s_4} = 5`, ordered toward the 5-edge. This is
  `h3-deligne-complex-upward-flag-toward-5-edge`.
- Hypothesis (b) is `h4-deligne-complex-bottom-triples-have-upper-bounds`.
