---
rg: 2
id: leavitt-free-group-leading-term-forces-linear-depth
kind: claim
title: A binary Leavitt unit with a persistent free-group leading term has linearly growing depth
distinct_from:
  leavitt-units-of-infinite-order-have-linear-depth-growth: that is the conjecture for all infinite-order units; this is a proved sufficient criterion that reduces it to units whose leading coefficients are nilpotent for every bi-invariant order.
  thompson-elements-are-undistorted-in-leavitt-unit-group: that uses germs at periodic points of Thompson elements; this uses the free-group grading of the algebra and applies to linear units.
---

**ESTABLISHED** by `leavitt-free-group-leading-term-forces-linear-depth-proof`.

Let `R = L_(F_2)(1,2)` be graded by the free group `F = <x_0, x_1>` with `deg s_i = x_i` and
`deg t_i = x_i^(-1)`, so that `deg s_μ t_ν = x_μ x_ν^(-1)`. Each homogeneous component is
`R_g = s_μ D t_ν`, where `D = span{ s_w t_w }` is the algebra of locally constant functions on the Cantor
set and `μ, ν` have no common last letter.

**Criterion.** Let `u` be in `R^x`, `k >= 1`, and `<` a bi-invariant order on `F`. Let `g = x_μ x_ν^(-1)` be
the `<`-largest element of the support of `u^k`, and write `(u^k)_g = s_μ 1_E t_ν`. Suppose that `g != 1`, that
one of `μ, ν` is the other followed by a nonempty word `γ`, and that `γ^∞` lies in `E`. Then
`lambda(u) >= 1/(2k)`, where `lambda(u) = lim_m max(ell(u^m), ell(u^-m))/m` and `ell` is the depth.

**Dichotomy for leading coefficients.** A homogeneous `y = s_μ 1_E t_ν` with `g != 1` is nilpotent iff
- `μ` and `ν` are incomparable, in which case `y^2 = 0`; or
- they are comparable and `E` misses the periodic point `γ^∞`.

So a unit with `lambda(u) = 0`, such as a Heisenberg center, has a nilpotent leading coefficient in every power
and for every bi-invariant order on `F`.
