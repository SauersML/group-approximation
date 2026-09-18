---
rg: 2
id: capacity-chain-resolvent-ring-has-rational-k0
kind: claim
title: The capacity-chain resolvent ring is finitely presented and simple, gets Q from a resolvent vacuum, and has [1] of infinite order and divisible by every n in K_0
distinct_from:
  fp-simple-resolvent-ring-with-divisible-unit-class: that is the design target, with a finitely generated K_2 condition; this is one explicit candidate for its conditions 1-4.
  leavitt-resolvent-ring-is-fp-simple-of-char-zero: R_L has every letter available everywhere, a Leavitt tuple, so [1] = 0; here availability depends on registers, and the resulting correspondence has index 1 on [1].
  resolvent-vacuum-rings-have-no-k0-state: that forces any such ring to be stateless; this candidate is consistent with it, being purely infinite by design.
---

**OPEN.** The ring `R_cap` below is finitely presented, simple and purely infinite. It
contains `Q` through a resolvent vacuum. In `K_0(R_cap)`, `[1] = −V_0` has infinite order
and is divisible by every `n`, so `R_cap ≅ M_n(R_n)` for every `n`. By
`resolvent-vacuum-rings-have-no-k0-state`, `R_cap` is then stateless.

## The mechanism: "v_k emits k+1 edges" with finitely many letters
- **The obstruction to overcome.** With finitely many letters, no state can emit, or
  receive through one letter, `k+1` edges for unbounded `k`.
- **The fix.** A *capacity* register makes the number of available continuations
  level-dependent. From a level-`k` state, the admissible prefixes are `d c^j st` for
  `0 <= j <= k`. That is `k+1` distinct paths, each ending in a level-`(k+1)` state. The
  letter `c` is available only while the capacity `Δ` is positive.
- **Future semantics.** As for `R_L`, registers are functions of the infinite future path:
  `X(xξ) = σ_x(X)(ξ)`.

## Design
**Types and registers.** There are two state types, `v` and `u`, with idempotents `p_v`
and `p_u` summing to `1`. At `v` the register is `N`, the level. At `u` the registers are
`L`, the level, and `Δ`, the capacity. The model has `0 <= Δ <= L`.

**Letters.** Each letter `x` has a substitution `σ_x` and an availability condition on the
rest of the path.

| letter | type | substitution | available when |
|---|---|---|---|
| `ℓ` | `v -> v` | `N ↦ N` | always |
| `b` | `v -> v` | `N ↦ N` | `N = 0` (a second loop at level `0`, and the anchor) |
| `a` | `v -> v` | `N ↦ N + 1` | always |
| `d` | `v -> u` | `N ↦ L` | always |
| `c` | `u -> u` | `L ↦ L`, `Δ ↦ Δ − 1` | `Δ >= 1` |
| `st` | `u -> v` | `L ↦ N − 1`, `Δ ↦ N − 1` | `N >= 1` |
| `a_u` | `u -> u` | `L ↦ L + 1`, `Δ ↦ Δ + 1` | always |

**Model.** Take the legal infinite words with tail `b^∞`, where `N(b^∞) = 0`. That is the
anchor, as `2^∞` is for `R_L`.
- Tails are closed under prepending legal letters and under deleting the first letter.
- Every `u`-path reaches `st`, because `Δ` decreases along `c` and `c` stops at `Δ = 0`.

**Base ring B (generators).**
- At `v`: `N`, `e_N = [N = 0]`, `N' = 1/N` off level `0`, and `A = (N+1)^(-1)`.
- At `u`: `L`, `Δ`, `e_Δ = [Δ = 0]`, and `Δ' = 1/Δ` off `Δ = 0`.
- Relations: `e^2 = e`, `e N = 0`, `N N' = p_v − e_N`, and the same for `Δ`;
  `A(N+1) = p_v = (N+1)A`.

**Relations of `R_cap`, finitely many.**
- (CK) `p_v = s_ℓ t_ℓ + s_b t_b + s_a t_a + s_d t_d` and `p_u = s_c t_c + s_st t_st + s_(a_u) t_(a_u)`.
- (Avail) `t_x s_y = 0` for `x ≠ y`, and `t_x s_x = p_(r(x))` for `x ∈ {ℓ, a, d, a_u}`.
  Also `t_b s_b = e_N`, `t_c s_c = p_u − e_Δ` and `t_st s_st = p_v − e_N`.
- (Cov) Each `B`-generator commutes with every range projection `s_x t_x`. Also
  `t_x X s_x = σ_x(X)·t_x s_x` wherever the table gives `σ_x(X)` as a polynomial.
- (Pos) `t_d e_N s_d ≤ e_Δ`, that is `[L = 0] ≤ [Δ = 0]`. The letter `a_u` transports this
  one identity to `[L = k]·[Δ >= k+1] = 0` for every `k`, which is the positivity
  constraint `Δ <= L`. That is why `a_u` is included.

**Q from a resolvent vacuum.** Put `E = e_N`, `x_m = s_a^(m−1) e_N` and
`y_m = e_N t_a^(m−1)`. Then `y_m x_m = E`, `N x_m = (m−1) x_m` and `y_m N = (m−1) y_m`.
Hence `m · (y_m A x_m) = E`, exactly as for `R_L`. If `R_cap` is simple, then
`Q ⊆ Z(R_cap)`.

## K_0 bookkeeping (heuristic)
This assumes `K_0(R_cap) = coker(1 − Φ)` on classes of `B`-idempotents, as in the
Ara--Brustenga--Cortiñas corner-skew-Laurent sequence
(`abc-twisted-laurent-k-theory-fibration`). That needs the core to be a filtered colimit
of regular supercoherent rings.
- **Classes.** `V_k = [v, N = k]`, `U_(m,L) = [u, Δ = m, level L]`, `X = [p_v]`, `Y = [p_u]`.
- **u-relations.**
  `U_(m,L) = [m<L] U_(m+1,L) + [m=L] V_(L+1) + [m>=1] U_(m−1,L−1)`, from the first letters
  `c`, `st`, `a_u`. This gives:
  - `Σ_m U_(m,0) = V_1`;
  - `Σ_m U_(m,1) = 2V_2 + 2V_1`;
  - `Σ_m U_(m,2) = 3V_3 + 5V_2 + 5V_1`.
- **v-relations, level `k`.** `V_k = [k>=1] V_(k−1) + V_k + [k=0] V_0 + D_k`, where
  `D_k = Σ_m U_(m,k)` and the four terms are the `a`, `ℓ`, `b` and `d` parts.
  - Level `0`: `V_1 = −V_0`.
  - Level `1`: `D_1 = −V_0`, so `V_2 = V_0/2`.
  - Level `2`: `D_2 = −V_1 = V_0`, so `V_3 = 7V_0/6`.
  - In general the recursion puts every `V_k` in `Q·V_0`. That every `n` occurs among the
    denominators, so that `V_0` is divisible by every `n`, is checked here only for
    `k <= 3` in this variant; it is part of item 3.
- **Totals.** `X = X + X + V_0 + Y`, from the `a`, `ℓ`, `b` and `d` parts, so
  `Y = −X − V_0`. Hence `[1] = X + Y = −V_0`: divisible, and of infinite order unless
  further relations kill it.
- **Without `a_u`.** The `u`-relations simplify to `D_k = (k+1) V_(k+1)` and
  `(k+1) V_(k+1) = −V_(k−1)`. Then `V_(2j) = ±V_0/(2^j j!)` and
  `V_(2j+1) = ±V_0/(2j+1)!!`, with the same conclusion `[1] = −V_0`. That variant lacks the
  finitely presented positivity relation. There every `n` does occur as a denominator.
  So a fallback is a variant without `a_u` in which positivity is achieved differently.

## What remains (all open)
1. **Presentation.** The finitely many relations present the Cuntz--Pimsner ring over the
   concrete base `B`, whose idempotents are the level and capacity indicators. The key
   points are that (Pos) plus the `a_u`-transport generate every positivity identity, and
   that transported idempotents commute.
2. **Simplicity.** A version of `leavitt-nekrashevych-completion-simplicity-criterion` for
   non-unital `ψ`, meaning letters with availability idempotents. Cofinality holds because
   `a` lowers the level in forward time. Every cycle has exits.
3. **K_0.** Justify the corner-skew-Laurent sequence for the core, and compute the full
   cokernel. This goes to lane `gq-k2-q`.
