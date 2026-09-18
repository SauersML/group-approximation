---
rg: 2
id: houghton-polynomial-dehn-by-ray-count
kind: route
title: Split by the number of rays, into n >= 5 (proved), n = 4 and n = 3
target: houghton-groups-have-polynomial-dehn-function
requires:
  - houghton-groups-with-five-or-more-rays-have-polynomial-dehn
  - houghton-group-h4-has-polynomial-dehn-function
  - houghton-group-h3-has-polynomial-dehn-function
---

Every `n >= 3` satisfies `n >= 5`, `n = 4` or `n = 3`. The three prerequisites give
a polynomial bound `δ_(H_n) ≼ x^(d_n)` in each case. The target asks for such a
`d_n` for each `n`, not a uniform one, so the cases combine directly.

The prerequisites can fail independently:

- `n >= 5` is proved with one auxiliary ray;
- `n = 4` still has route changes, but no auxiliary ray;
- `n = 3` has no route changes at all.
