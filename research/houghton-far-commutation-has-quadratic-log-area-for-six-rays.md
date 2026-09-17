---
rg: 2
id: houghton-far-commutation-has-quadratic-log-area-for-six-rays
kind: claim
title: "For n >= 6, commuting the top transposition of H_n past one pushed k steps down a ray has area O(k^2 log k)"
artifacts:
  - research/artifacts/zp-houghton-pours-2026-09-17.md
distinct_from:
  houghton-far-transposition-commutation-is-superpolynomial: that asserts superpolynomial area for this family in some H_n with n >= 3; this proves an O(k^2 log k) upper bound for every n >= 6, so any such H_n must have n in {3,4,5}.
  houghton-transposition-commutation-area-is-polynomial: that asks for a polynomial bound over all words centralizing α, for every n >= 3; this bounds one explicit far-commutation family, and only for n >= 6.
---

Let `n >= 6` and give `H_n` Lee's presentation (arXiv:1212.0257, Theorem C), with
generators `g_i = λ_(1,i+1)` and `α = ((1,1),(1,2))`, and `x^h = h^(-1) x h`. Then
there is `C` such that for all `k >= 1`

```text
Area( [α, α^(g_1^(-k))] ) <= C k^2 (1 + log k).
```

The second factor is the transposition `((1,k+1),(1,k+2))`.

More generally, let `W(m)` be the largest area of changing the route ray `c` of a
pour `λ_ac^m λ_cb^m`. Then `W(m) ≼ m^2 log m`. Rerouting a transposition pushed `k`
steps down a ray costs `≼ k^2 log k`.
