---
rg: 2
id: thompson-f-ore-radius-function-is-not-quasi-polynomial
kind: claim
title: For every field K the Ore radius function of K[F] exceeds exp_j((log_j R)^c) infinitely often, so no common-multiple scheme with quasi-polynomial radius control can prove F amenable
distinct_from:
  thompson-f-cardinality-certificates-need-tower-degree: that bounds only cardinality certificates (non-doubling monomial sets) and says in its Scope that linear-algebra solutions a u = b v are unconstrained; this constrains every common multiple, however found, through its support radius.
  thompson-f-ore-obstructions-must-see-finite-support: that says obstructions to the Ore condition must depend on finite supports; this is a quantitative lower bound on how far the supports of common multiples must spread.
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound on Følner sets; this transfers it to the group ring through ore-radius-function-bounds-folner-radius.
  thompson-f-amenable-iff-group-ring-is-ore: that is Kielak's qualitative equivalence; this shows that the Ore side of the equivalence, if true, is quantitatively non-elementary.
artifacts:
  - experiments/ore-radius-folner-2026-09-17/check_local_bartholdi.py
---

**ESTABLISHED** through `thompson-f-ore-radius-function-is-not-quasi-polynomial-proof` (direct proof
from `ore-radius-function-bounds-folner-radius`, Moore's theorem and bi-orderability; not independently
reviewed; swarm-0917, c-famen).

Let `S = {1, x_0^±1, x_1^±1} ⊆ F`, `B(R) = S^R`, and let `Ω_K(R) ∈ N ∪ {∞}` be the Ore radius of `K[F]`
(claim `ore-radius-function-bounds-folner-radius`): the least `ρ` such that all nonzero
`a, b ∈ K[B(R)]` have nonzero `t, u ∈ K[B(ρ)]` with `a t = b u`. Let `exp_0(x) = x`,
`exp_(i+1)(x) = 2^(exp_i(x))`, and let `log_j` be the `j`-fold iterated `log_2`.

**Theorem B (explicit form).** Let `C > 1` be Moore's constant for `Γ = {x_0^±1, x_1^±1}`. Suppose
`Ω_K(R) < ∞` for all `R`, and put `τ(R) = R + Ω_K(R)`. For `k >= 1` let:
- `n = |B(k)|`, so `5 <= n <= 5^k`;
- `r = H_n n! + 1`;
- `d = 1` if `K` is infinite, else `d = n^2 + ⌈log_2 r⌉ + 1`.

Then `exp_m(0) <= 5^(τ^((r-1)d)(k))` for every integer `m >= 0` with `16 C^m ln(1 + k ln 5) <= k`.

**Corollary (class kill).** For every field `K` and all integers `j >= 1`, `c >= 1`, the inequality
`Ω_K(R) <= exp_j((log_j R)^c)` fails for infinitely many `R`. The corollary is unconditional:
- If some `Ω_K(R)` is infinite, it holds trivially, because `Ω_K` is nondecreasing. By
  `thompson-f-amenable-iff-group-ring-is-ore`, this is the non-amenable case.
- Otherwise Theorem B applies.

It covers:
- polynomial radius control `Ω(R) <= R^c`;
- quasi-polynomial control `2^((log R)^c)`;
- every fixed `exp_j((log_j R)^c)`.

**What this kills.** Take any scheme that proves the Ore condition for `K[F]` by producing, for each
pair `a, b` supported in `B(R)`, a common multiple whose radius is bounded by a function in this class.
Examples are explicit identities with polynomially many letters, bounded-depth recursions on forest
diagrams, and linear algebra in degrees `poly(R)`. Every such scheme proves a false inequality.
- *Invariant:* the Ore radius function `Ω_K` against Moore's tower.
- *Step where every member dies:* feeding `Ω` into Bartholdi's `(r-1) × r` matrix with `n = |B(k)|`
  and eliminating produces a set with `|B(1)F| < (1 + δ)|F|`, `δ = O(log k / k)`, inside a ball of
  radius `exp_(j+4)(3k+1)`. That set is `O(log k / k)`-Følner and has at most `exp_(j+5)(3k+2)`
  elements, while Moore demands a tower of height about `log_C k`.

**Scope.**
- Exponential control `Ω(R) <= 2^R`, and even `2^(R^ε)`, is **not** excluded. The elimination depth
  is `r ~ n! ~ exp_2(O(k))`, and iterating an exponential that many times gives a tower of height
  about `exp_2(k)`, far above Moore's height `log_C k`.
- The statement concerns radius, not degree in the positive monoid, and only the fixed generating set
  `S`. Changing generators changes `Ω` by composing with a linear map, and the class is closed under
  that.
- `Moore's C` is not explicit, so no specific `R` is identified.
- Nothing is said about `P_(2,2)` or any single pair: a single pair can have a small common multiple.
