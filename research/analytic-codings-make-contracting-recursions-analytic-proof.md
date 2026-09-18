---
rg: 2
id: analytic-codings-make-contracting-recursions-analytic-proof
kind: route
title: The recursion transports each breakpoint t to g_u(t), and the orbit of a point other than the fixed point is infinite
target: analytic-codings-make-contracting-recursions-analytic
---

Notation is as in the target claim.

**Item 1 (the fixed point).** `ψ` is continuous and `C_n` is compact, so `ψ` is uniformly
continuous. The cones `u^k C_n` shrink to the point `u^∞`, so the intervals
`g_u^k(J) = ψ(u^k C_n)` are nested with diameters tending to `0`. Their intersection is the single
point `p = ψ(u^∞)`.
- `g_u(p) = ψ(u·u^∞) = p`, so `p` is fixed.
- A point `q ∈ J` with `g_u^m(q) = q` for some `m ≥ 1` lies in every `g_u^(km)(J)`, so `q = p`.

So `p` is the only periodic point of `g_u` in `J`.

**Item 2 (breakpoints).** Let `B` be the finite set of breakpoints of `Y`, and suppose
`t ∈ B` with `t ≠ p`. Put `t_1 = g_u(t)`.
- `t_1` is an interior point of `J`, because `g_u` is a diffeomorphism onto its image and `t` is
  interior.
- Suppose `Y` were analytic at `t_1`. For `t'` near `t` we have `g_u(t')` near `t_1`, and the
  recursion gives `Y(t') = g_v^(−1)(Y(g_u(t')))`. Here `g_v^(−1)` is analytic on a neighbourhood of
  `g_v(J)`, which contains `Y(g_u(t')) = g_v(Y(t'))`. So `Y` would be analytic at `t`, a
  contradiction. Hence `t_1 ∈ B`.
- `t_1 ≠ p`: otherwise `g_u(t) = p = g_u(p)` and injectivity gives `t = p`.

Iterating, `g_u^k(t) ∈ B` for every `k ≥ 0`. These points are pairwise distinct: an equality
`g_u^k(t) = g_u^j(t)` with `k > j` makes `g_u^j(t)` periodic, hence equal to `p`, hence `t = p`.
So `B` is infinite, which contradicts piecewise analyticity. Therefore `B ⊆ {p}`, and `Y` is
analytic on `[a, p]` and on `[p, b]`. ∎

**Corollary.**
- **`Y` is analytic on `S`.** If `p` lies in the interior of `g_w(J)`, then `Y = g_z ∘ g_w^(−1)` near
  `p`, so `p` is not a breakpoint and `Y` is analytic on `J = S`. Otherwise `S` is a side, and
  Item 2 applies.
- **`Y = Φ` on `S`.** `Y` agrees with `g_z ∘ g_w^(−1)` on the nondegenerate interval
  `g_w(J) ⊆ S`. The identity theorem, on the connected set `S`, gives `Y = Φ` there.
- **The recursion for `Φ`.** For `x ∈ S` with `g_u(x) ∈ S`, the recursion reads
  `Φ(g_u(x)) = Y(g_u(x)) = g_v(Y(x)) = g_v(Φ(x))`. ∎
