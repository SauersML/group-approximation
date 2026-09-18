---
rg: 2
id: register-comparison-presentations-are-not-simple-proof
kind: route
title: Base-closure elements are constructible piecewise-rational in the registers, so relations true on dense integral values also hold on generic chains
target: register-comparison-presentations-are-not-simple
requires:
  - capacity-chain-presentation-is-not-simple
---

Lane proof, not independently reviewed. Notation as in the claim. `K` denotes a field
containing `Q`, and points `y ∈ K^(Y_ρ)` are register assignments.

## 1. Value functions
**Lemma 1.** For every `f ∈ ℬ` at type `ρ` there is a function `F_f` on `K^(Y_ρ)`, depending
only on `𝒫` and defined wherever the resolvents involved are nonzero, such that:
- (a) `f` acts on every state `η` of type `ρ`, in every diagonal module, as the scalar
  `F_f(v(η))`;
- (b) `F_f` is **constructible piecewise-rational**. That is, there is a finite partition
  of `K^(Y_ρ)` into sets `C_1..C_m`, each a Boolean combination of zero sets `{P = 0}` with
  `P ∈ Z[Y_ρ]`, and on each `C_j`, `F_f = a_j/b_j` with `a_j, b_j` polynomials and `b_j`
  nowhere zero on `C_j`.

*Proof.* By induction on how `f` is built.
- **Base generators.**
  - A register `Y` gives `F = Y`, with one piece.
  - An indicator `e_P` gives `[P = 0]`, with pieces `{P = 0}` and `{P ≠ 0}`.
  - A reciprocal `P'` gives `0` on `{P = 0}` and `1/P` off it.
  - A resolvent `Q^(-1)` gives `1/Q` on `{Q ≠ 0}`.
- **Sums and products.** Take the common refinement of the two partitions.
- **Transports.** Let `f` be at type `s(x)`. Then `t_x f s_x` acts on `η` of type `r(x)`:
  `s_x η = xη` when `α_x(v(η)) = 1`, and `0` otherwise. And `v(xη) = σ_x(v(η))`. So
  `F_(t_x f s_x)(y) = α_x(y)·F_f(σ_x(y))`.
  - `α_x` is a Boolean polynomial in indicators, so it is constant on the cells of a
    constructible partition.
  - The preimage of `{P = 0}` under the polynomial map `σ_x` is `{P∘σ_x = 0}`, so
    preimages of constructible cells are constructible.
  - On a pulled-back cell, `F_f∘σ_x = (a_j∘σ_x)/(b_j∘σ_x)`, and `b_j∘σ_x` is nowhere zero
    there.

  Transports along words are iterates of this step. ∎

**The generic cell.** `K^(Y_ρ)` is irreducible, and the cells are constructible and finite
in number. So exactly one cell `C_f` contains a nonempty Zariski-open set. Choose a nonzero
`P_f ∈ Z[Y_ρ]`, with the resolvents of `f` among its factors, such that `{P_f ≠ 0} ⊆ C_f`.
Write `g_f = a/b` for the rational function on `C_f`.

## 2. Density
**Lemma 2.** If `f ∈ ℬ` at type `ρ` acts as `0` on `M_Z`, then `g_f = 0`. Hence
`F_f(y) = 0` at every `y` with `P_f(y) ≠ 0`.

*Proof.*
- **Density survives the cut.** The `ρ`-values of `M_Z` are Zariski dense (C3). Removing
  the proper closed set `{P_f = 0}` leaves a set `S` that is still dense, because an
  irreducible space is not the union of two proper closed subsets.
- **The rational function vanishes.** On `S`, `a/b = F_f = 0` by Lemma 1(a), so `a`
  vanishes on a dense set. Hence `a = 0` and `g_f = 0`. ∎

## 3. Proof of the statement
- **The finitely many polynomials to avoid.** Let `f_1..f_q` be the extra relations and
  `Q_1..Q_r` the extra resolvents, and put `P_* = Π P_(f_j) · Π Q_i`.
- **Choosing k.** By the third bullet of (C4), only finitely many `k ∈ K` have a
  `δ`-dependent value of `M_k` at which `P_*` vanishes. Fix `k` outside that set.
- **Part 1: `M_k` satisfies the full presentation.**
  - *At a `δ`-dependent value `y`.* `P_(f_j)(y) ≠ 0`, so `F_(f_j)(y) = 0` by Lemma 2, and
    `Q_i(y) ≠ 0`, so the resolvents act by `1/Q_i(y)`.
  - *At a `δ`-free value.* The value is a value of `M_Z` (C4), where every `f_j` vanishes
    and every `Q_i` is nonzero.
  - *The remaining relations* (D1)–(D6) hold by (C4).

  So `M_k` is a module of `𝒫` with its extra relations and resolvents.
- **Part 2: `X_k` separates.**
  - *On a chain state.* `L = k` and `Δ = δ − n ∉ Z`, so `λ_k = 1` and every `ε_i = 0`,
    and `X_k = 1`.
  - *On a `τ`-state of `M_Z` with `L = k`.* `Δ ∈ F_k` by (C2), so `Σ ε_i = 1` and
    `X_k = 0`.
  - *On every other state of `M_Z`.* `λ_k = 0`.

  Hence `X_k ≠ 0` in `R(𝒫)`, while its image in `R_conc` is `0`. The kernel is a nonzero
  ideal, proper because `R_conc ≠ 0`. ∎

## 4. The capacity-chain instance
Take the presentation of `capacity-chain-resolvent-ring-has-rational-k0`, with or without
`a_u`, with `τ = u`, `K = Z_(>=1)` and `F_k = {0..k}`.
- **(C1).** `σ_c(Δ) = Δ − 1`, `σ_c(L) = L`, and `α_c = p_u − e_Δ` is `1` whenever
  `Δ ≠ 0`.
- **(C2).**
  - `ε_i = t_c^i e_Δ s_c^i` acts at `η` as `[Δ(η) = i]`. The prefixes `c^j η`, `j < i`,
    are legal exactly when `Δ(η), …, Δ(η) − i + 1 ≠ 0`, and then `e_Δ(c^i η) = [Δ(η) = i]`.
  - `λ_k = t_d t_st ε_(k−1) s_st s_d` acts as `[L = k]`. The prefix `d` is always legal,
    `st` is legal when `N(dη) = L(η) ≠ 0`, and then `Δ(st dη) = L(η) − 1`.
  - Concretely, `u`-values are `0 <= Δ <= L`, so `F_k = {0..k}`.
- **(C3).** The `v`-values `N ∈ Z_(>=0)` are dense in `Q`. The `u`-values, the integer
  triangle `{0 <= Δ <= L}`, are dense in `Q^2`.
- **(C4).** Take `M_k` to be the module of `capacity-chain-presentation-is-not-simple-proof`
  over `Q(δ)`, with `δ` transcendental in place of `1/2`. Its §2 verification applies
  unchanged, since only `Δ ≠ 0` on the chain is used. By induction on prefixes:
  - every `v`-value is an integer `N >= 0`, a value of `M_Z`;
  - every `u`-value is either `(δ + j, k')` with `j ∈ Z` and `k' >= k`, reached through `c`
    and `a_u` from the chain, or an integer triangle point, reached after an `st`, since
    `c` is blocked at `Δ = 0` and `a_u` preserves `Δ <= L`. Triangle points are values
    of `M_Z`;
  - for a nonzero `P ∈ Z[Δ, L]`, `P(δ + j, k') = 0` iff `P(t, k') ≡ 0` in `t`, iff
    `(L − k') | P`. That holds for at most `deg_L P` integers `k'`. Since `k' >= k`, only
    finitely many `k` are affected.

So the capacity-chain presentation stays non-simple after adding any finitely many
commutative relations true in its concrete model, and any finitely many resolvents
nonzero there.
