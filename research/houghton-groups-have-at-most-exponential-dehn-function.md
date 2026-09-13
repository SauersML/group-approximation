---
rg: 2
id: houghton-groups-have-at-most-exponential-dehn-function
kind: claim
title: "Lee: for every n >= 3 the Dehn function of Houghton's group H_n is at most exponential"
distinct_from:
  houghton-groups-have-polynomial-dehn-function: that asks for a polynomial upper bound, which is open; this records the known exponential upper bound.
---

For every `n >= 3`, `δ_(H_n)(x) ≼ e^x`.

S. R. Lee, *Geometry of Houghton's groups*, arXiv:1212.0257, Theorem D:
"For any n≥3 the Dehn function δ_{ℋ_n}(x) of ℋ_n satisfies δ_{ℋ_n}(x) ≼ e^x."
The same paper gives the finite presentation (Theorem C, Theorem 2.14):
generators `g_1, ..., g_(n-1), α` with relators `α^2`, `(α α^(g_1))^3`,
`[α, α^(g_1^2)]`, `[g_i, g_j] = α` for `i < j`, and
`α^(ḡ_i) = α^(ḡ_j)` for `i < j`, where `g^h = h^(-1) g h` and
`ḡ = g^(-1)`. Here `g_i` translates along the line formed by rays `1` and
`i+1`, and `α` is the transposition of `(1,1)` and `(1,2)`.
