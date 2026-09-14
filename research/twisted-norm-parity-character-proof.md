---
rg: 2
id: twisted-norm-parity-character-proof
kind: route
title: Apply theta to sigma(a) a = h^2
target: twisted-norm-equation-dies-under-invariant-parity-character
requires:
  - index-two-strong-atiyah-is-a-twisted-norm-equation
---

By [[index-two-strong-atiyah-is-a-twisted-norm-equation]], `G` satisfies Strong Atiyah
over `K` iff no `a` in `D_K(N)` has `sigma(a) a = h^2`.

Suppose `a` is a solution. `h^2` is a group element, hence nonzero, so `a != 0`, and
`a` is a unit of the division ring `D_K(N)`. So is `sigma(a)`. Apply `theta`:

    theta(h^2) = theta(sigma(a)) + theta(a) = theta(a) + theta(a) = 0,

using `theta o sigma = theta`. This contradicts `theta(h^2) = 1`. So there is no
solution.
