---
rg: 2
id: thompson-f-ore-x0-components-meet-no-later-proof
kind: route
title: The x_0-count is a grading of K[M], K[M] has no zero divisors, so extreme components of a common multiple are common multiples of extreme components
target: thompson-f-ore-x0-components-meet-no-later
requires:
  - thompson-f-is-bi-orderable
artifacts:
  - research/artifacts/ideas-f-hyperbolic-2026-09-13.md
---
Notation as in the claim.

**Step 1 (the x_0-count is additive).** Define `α(x_0) = (1, 0)` and `α(x_i) = (0, 1)` for `i >= 1`. Each
relation `x_j x_i = x_i x_(j+1)` with `i < j` has both sides of the same value: `(1, 1)` when `i = 0`
(because `j >= 1` and `j + 1 >= 2`), and `(0, 2)` when `i >= 1`. So `α` extends to a monoid homomorphism
`M -> N^2`. Any word representing `w`, in particular its normal form, has `α(w) = (ν_0(w), deg(w) - ν_0(w))`.
Hence `ν_0(w w') = ν_0(w) + ν_0(w')`, and `K[M]` is graded by `(degree, ν_0)`: the product of a component of
level `e` with one of level `e'` lies in level `e + e'`.

**Step 2 (no zero divisors).** `F` is bi-orderable (`thompson-f-is-bi-orderable`). A group ring of an
orderable group over a field has no zero divisors: the product of the order-largest terms of two nonzero
elements survives in their product (standard; e.g. Passman, *The algebraic structure of group rings*,
not re-read here). So `K[F]`, and with it `K[M] ⊆ K[F]`, has no zero divisors.

**Step 3 (extreme components).** Suppose `a u = b v` with `u, v` nonzero homogeneous of degree `k`. Write
`u = Σ u_e` and `v = Σ v_e`. By Step 1, `a u = Σ_(e, e') a_e u_(e')` has component of level `e` equal to
`Σ_(e' + e'' = e) a_(e') u_(e'')`. The largest level that occurs is `e_max(a) + e_max(u)`, and there the only
contribution is `top(a) top(u)`, which is nonzero by Step 2. Likewise the largest level of `b v` is
`e_max(b) + e_max(v)`, with component `top(b) top(v) ≠ 0`. Since `a u = b v`, the largest levels agree and so
do the components there: `top(a) top(u) = top(b) top(v)`. The elements `top(u), top(v)` are nonzero and
homogeneous of degree `k`, because components of a homogeneous element keep its degree. So
`δ(top(a), top(b)) <= k`. The same argument with smallest levels gives `bot(a) bot(u) = bot(b) bot(v)` and
`δ(bot(a), bot(b)) <= k`.

**Step 4.** Taking `k = δ(a, b)` gives both inequalities. If `δ(a, b) = ∞` there is nothing to prove. If
`top(a) = top(b)`, then `u = v = 1` gives `δ = 0`. ∎
