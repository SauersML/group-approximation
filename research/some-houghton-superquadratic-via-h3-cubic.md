---
rg: 2
id: some-houghton-superquadratic-via-h3-cubic
kind: route
title: H_3 has at least cubic Dehn function, so some Houghton group is not quadratic
target: some-houghton-group-has-superquadratic-dehn-function
requires:
  - houghton-group-h3-has-at-least-cubic-dehn-function
---

Take `n = 3`. By `houghton-group-h3-has-at-least-cubic-dehn-function`,
`x^3 ≼ δ_(H_3)(x)`.

Suppose `δ_(H_3)(x) ≼ x^2`. Then `x^3 ≼ x^2`, which means
`x^3 <= C (Cx + C)^2 + Cx + C` for some `C` and all `x`. This fails for large
`x`. So `δ_(H_3)(x) ≼ x^2` fails, and `H_3` witnesses the claim. ∎

As a consequence, `houghton-groups-have-quadratic-dehn-function` is false: it
asserts `δ_(H_3) ≃ x^2`.
