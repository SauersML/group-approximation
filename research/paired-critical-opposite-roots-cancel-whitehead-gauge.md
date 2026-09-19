---
rg: 2
id: paired-critical-opposite-roots-cancel-whitehead-gauge
kind: route
title: Exit and return through the critical opposite root to cancel the Whitehead gauge
target: el20-six-moving-coefficient-square-bridges
requires:
  - one-nonnormal-dressing-cannot-preserve-moving-full-gram
---

This route proposed using two genuinely nonnormal letters in the critical
opposite-root subgroup `x_82(R)`: the first exits the Hecke atom normalizer,
the second returns, and the resulting normalizer was meant to carry the
inverse Whitehead reservoir action.

It is invalidated by
`paired-critical-opposite-roots-return-only-trivially`.  Root additivity
reduces the pair to `x_82(a+b)`, and the exact `(2,8)` block calculation
shows that membership in the constant Hecke normalizer forces `a+b=0`.
The returned normalizer is therefore the identity, so it has no reservoir
action available to cancel the Whitehead gauge.

This invalidation is deliberately narrow.  It does not address a pair in
different root channels or a longer return word with an intervening
coefficient occurrence.
