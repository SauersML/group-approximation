---
rg: 2
id: thompson-f-ore-x0-components-meet-no-later
kind: claim
title: Top and bottom x_0-components of a pair in K[M] have a common right multiple no later than the pair itself
distinct_from:
  thompson-f-p22-over-f2-exhaustive-degree-seven-census: that counts minimal common-multiple degrees of P_(2,2) pairs over F_2; this is a field-independent inequality between the degree of any pair and the degrees of its extreme x_0-components
  thompson-f-amenable-iff-group-ring-is-ore: that equates amenability of F with the Ore condition for K[F]; this only compares Ore degrees of a pair and of its graded components
artifacts:
  - research/artifacts/ideas-f-hyperbolic-2026-09-13.md
---
**ESTABLISHED** through `thompson-f-ore-x0-components-meet-no-later-proof` (elementary; not independently
reviewed; no priority claimed).

**Setting.** `K` is a field and `M` the positive monoid of Thompson's group `F`, with generators
`x_0, x_1, ...`, relations `x_j x_i = x_i x_(j+1)` for `i < j`, and normal forms `x_(i_1) ... x_(i_d)` with
`i_1 <= ... <= i_d`. For a monoid element `w` let `ν_0(w)` be the number of letters `x_0` in its normal form.
Every nonzero homogeneous `c ∈ K[M]` splits as `c = Σ_e c_e`, where `c_e` collects the monomials with
`ν_0 = e`. Put `top(c) = c_(e_max)` and `bot(c) = c_(e_min)`, the nonzero components of largest and smallest
level. For nonzero homogeneous `a, b ∈ K[M]` let `δ(a, b)` be the least `k` such that `a u = b v` for some
nonzero homogeneous `u, v ∈ K[M]` of degree `k`, or `∞` if there is none.

**Statement.** For all nonzero homogeneous `a, b ∈ K[M]`:

- `δ(top(a), top(b)) <= δ(a, b)`;
- `δ(bot(a), bot(b)) <= δ(a, b)`.

When the two components coincide the left side is `0`.

**Use.** A pair of extreme components with no common right multiple certifies the same for the pair. The
converse direction gives nothing: components can meet while the pair does not.
