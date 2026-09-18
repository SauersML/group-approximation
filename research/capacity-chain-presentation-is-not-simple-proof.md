---
rg: 2
id: capacity-chain-presentation-is-not-simple-proof
kind: route
title: A module on words over a bi-infinite c-chain with non-integral capacity satisfies every relation but detects X_k
target: capacity-chain-presentation-is-not-simple
requires: []
---

*Wiring note (2026-09-18):* `capacity-chain-resolvent-ring-has-rational-k0` supplies notation only, namely the
presentation (CK), (Avail), (Cov), (Pos). The argument never uses its truth, which this route's target
refutes, so `requires` is empty.

Lane proof, not independently reviewed. Notation as in
`capacity-chain-resolvent-ring-has-rational-k0`. Fix an integer `k >= 1` and put
`δ = 1/2`.

## 1. The module
- **Basis.** `M` is the `Q`-vector space with basis `e_(w,n)`, where `n ∈ Z` and `w` is a
  finite word, not ending in `c`, that is *legal over the chain* in the sense below.
- **The chain.** The chain states are `e_(∅,n)`, of type `u`, with registers `L = k` and
  `Δ = δ − n`.
- **Letters.** `s_x e_(w,n) = e_(xw,n)`, except that `s_c e_(∅,n) = e_(∅,n+1)`. Each `t_x`
  deletes a leading `x`, or sends `e_(∅,n)` to `e_(∅,n−1)` when `x = c`, and is `0`
  otherwise.
- **Registers.** On `e_(xw,n)` the registers are `σ_x` of the registers of `e_(w,n)`, by
  the table. The `B`-generators act diagonally: `N`, `L`, `Δ` by their values, `e_N` by
  `[N = 0]`, `e_Δ` by `[Δ = 0]`, `N'` and `Δ'` by reciprocals off those sets, and `A` by
  `1/(N+1)`.
- **Legality.** `xw` is legal when the availability of `x` holds at `(w,n)`:
  - `c` needs `Δ ≠ 0`;
  - `st` needs `N ≠ 0`;
  - `b` needs `N = 0`;
  - the other letters are always available.

  In the ring, availability is exactly the idempotent `t_x s_x` of (Avail), so `Δ ≠ 0` is
  the correct reading. Nothing asks for `Δ >= 1`.
- **Values.** By induction:
  - `N` and `L` take values in `Z_(>=0)`: `L(st ξ) = N(ξ) − 1` with `N(ξ) >= 1`,
    `L(a_u w) = L(w) + 1`, and `L` is `k` on the chain.
  - `Δ` takes values in `δ + Z` on words that reach the chain through `c` and `a_u` only.
    It is an integer after an `st`.

  So every reciprocal used is defined.

## 2. The relations hold
- **(CK).** A `v`-vector `e_(w,n)` lies in exactly one range, that of the first letter of
  `w`. A `u`-vector lies in the range of its first letter, and the chain states lie in the
  range of `c`. The ranges are orthogonal.
- **(Avail).** `t_x s_x` is the projection onto the vectors at which `x` is available, by
  construction, and `t_x s_y = 0` for `x ≠ y`.
- **(Cov).** Diagonal operators commute with the range projections. `t_x X s_x` acts by
  `σ_x(X)` on the domain of `x`, by the recursive definition. On the chain this holds
  because `Δ(∅,n+1) = Δ(∅,n) − 1` and `L` is constant.
- **Base-ring relations.** `e_N N = 0`, `N N' = p_v − e_N`, `A(N+1) = p_v`, and the
  corresponding ones for `Δ`, all hold pointwise.
- **(Pos): `[L=0] ≤ e_Δ`.** Here `[L=0]` acts by `[N(dη)=0] = [L(η)=0]`. States with
  `L = 0` are of three kinds:
  - `st ξ` with `N(ξ) = 1`, where `Δ = 0`;
  - `c w` with `L(w) = 0`, which is illegal: by induction `Δ(w) = 0`, and `c` needs
    `Δ ≠ 0`;
  - none on the chain, where `L = k >= 1`, or after an `a_u`, where `L >= 1`.

  So `[L=0] ≤ e_Δ` holds.

## 3. X_k separates
- **In `R_abs`.** `[Δ = i] = t_c^i e_Δ s_c^i` and `[L = k] = t_d [N = k] s_d`, with
  `[N = k] = t_st [Δ = k−1] s_st` (for `k >= 1`). So `X_k ∈ R_abs`.
- **On `M`.** `X_k e_(∅,n) = e_(∅,n)`, because `L = k` and `Δ = 1/2 − n` is not in
  `{0..k}`. So `X_k ≠ 0`.
- **In `R_conc`.** On a legal `u`-word with tail `b^∞` and level `L = k`, the capacity
  lies in `{0..k}`: the chain from the word's `st` has `L − Δ` equal to the number of `c`'s
  and `a_u`-steps. So `X_k = 0` in `R_conc`.
- **Conclusion.** `R_abs -> R_conc` is a nonzero surjection with a nonzero kernel, so
  `R_abs` is not simple. Dropping `a_u` changes none of these steps. ∎
