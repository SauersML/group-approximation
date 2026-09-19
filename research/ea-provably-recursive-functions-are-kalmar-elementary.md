---
rg: 2
id: ea-provably-recursive-functions-are-kalmar-elementary
kind: claim
title: The provably recursive functions of IΔ0+Exp are exactly the Kalmár elementary functions, and each is bounded by a fixed tower exp_k
distinct_from:
  recursive-amenable-classes-have-uniform-folner-bounds: that is Cavaleri's recursive Følner bound for a c.e. class of amenable presentations; this is the classical proof-theoretic fact that a proof in elementary arithmetic yields an elementary witness function.
---

**ESTABLISHED by citation**, plus a one-paragraph bounding lemma proved here.

**Import (verbatim).** P. Henk, F. Pakhomov, *Slow and ordinary provability for Peano
Arithmetic*, arXiv:1602.01822v2 (6 Jun 2016), §2.1, pp. 8–9, read from the arXiv PDF on
2026-09-18:

> A recursive function f is said to be provably recursive in a theory S ⊇ I∆0+Exp if
> S ⊢ f↓. The provably recursive functions of I∆0+Exp are exactly the Kalmar elementary
> functions. The class of Kalmar elementary functions is the smallest class containing
> successor, zero, projection, addition, multiplication, substraction, and closed under
> composition as well as bounded sums and bounded products ([20]).

Here `f↓` is `∀x⃗ ∃y ϕ_f(x⃗, y)` for the natural Σ1 definition `ϕ_f` of `f` through Kleene's
normal form `f(n) = U(µy T(e,n,y))` (same section, eqs. (8)–(10)). The same section records
(p. 7): "Since the formula deﬁning exponentiation in I∆0 is ∆0, I∆0+Exp is a conservative
extension of Elementary Arithmetic (EA)". So everything below holds verbatim for EA
(also called EFA).

**Bounding lemma (proved here).** For every Kalmár elementary `f` there is `k` with
`f(x⃗) <= exp_k(m + 2)` for all `x⃗`, where `m = max x⃗` (and `m = 0` for constants).
Hence `f(n) <= exp_(k+1)(n)` for `n >= 2`, using `n + 2 <= 2^n`.

*Proof,* by induction along the definition quoted above. Write `T = exp_a(m+2) >= m + 2`
for `a >= 1`.
- Zero, successor, projections, addition and cut-off subtraction are `<= 2m + 1 <= 2^(m+2)`.
  Multiplication is `<= m^2 <= 2^(m+2)`, which holds for every `m >= 0`.
- Composition. If `g_i <= exp_a(m+2)` and `f <= exp_b(M+2)` with `M = max g_i`, then,
  since `t + 2 <= 2^t` for `t >= 2`, `f(g⃗) <= exp_b(exp_a(m+2) + 2) <= exp_(a+b+1)(m+2)`.
- Bounded sum over `i < y`, where `y <= m` is an argument. With `g <= T`, the sum is
  `<= y T <= T^2 <= 2^(T+2) <= 2^(2^T) = exp_(a+2)(m+2)`.
- Bounded product over `i < y`. It is `<= T^y <= T^T <= 2^(T^2) <= 2^(2^(2^T)) = exp_(a+3)(m+2)`.

Each step raises the level by a fixed amount, so every elementary function has some level `k`. ∎

Citation route: `ea-provably-recursive-functions-kalmar-citation`.
