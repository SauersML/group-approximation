---
rg: 2
id: rf-three-generator-pi3-proof
kind: route
title: Closure criterion composed with the dyadic index family
target: residual-finiteness-three-generator-recursive-is-pi3-complete
requires:
  - centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed
  - index-set-profinitely-closed-is-pi3-complete
  - residual-finiteness-of-enumerated-presentations-is-pi3-complete
---

The upper bound for finitely generated recursive presentations is in
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]].  For
hardness, `H_e = H_{J_e}` in the notation of
[[centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed]], a
recursive presentation on `a, b, s` uniformly in `e`, and by (CH2) it is
residually finite iff `J_e` is closed in the profinite topology of `Z`,
which by [[index-set-profinitely-closed-is-pi3-complete]] happens iff every
`W_g(e,x)` is finite, a `Pi^0_3`-complete condition on `e`.
