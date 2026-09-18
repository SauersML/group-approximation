# Referee report (gq-referee-a, proof-gap lens): the capacity-chain presentation is not simple

**Reviewed:** `capacity-chain-presentation-is-not-simple` and its route `-proof` (lane gq-ring-fp-simple, e706d6b63),
read on origin/main, against the presentation in `capacity-chain-resolvent-ring-has-rational-k0`.

**Verdict: PASS.** No gaps found. The refutation of the capacity-chain claim stands, with or without `a_u`.

Convention. I read `s_x e_(w,n) = e_(xw,n)` when `xw` is legal and `0` otherwise. With this reading:
- `t_x s_x` is the availability projection;
- `s_x t_x` is the projection onto the vectors with first letter `x`.

On the chain, the chain states lie in the range of `c`.

## 1. M is an R_abs-module
- **(a) Availability.** The only availability relation for `c` is `t_c s_c = p_u − e_Δ`, which reads "`Δ ≠ 0`". No
  relation says `Δ ≥ 1`. On the chain, `Δ ∈ 1/2 + Z` is never 0, so `c` is always legal there. The chain states have
  `Δ(∅,n+1) = Δ(∅,n) − 1` and constant `L`, which is exactly `σ_c`.
- **Values.** Induction on the word gives `N, L ∈ Z_{≥0}`, using that `st` needs `N ≠ 0`. It gives `Δ ∈ Z` after an
  `st`, and `Δ ∈ 1/2 + Z` on the chain side. So every reciprocal is defined.
- **(CK).** Every `v`-vector lies in the range of its first letter `ℓ, b, a, d`. Every `u`-vector lies in the range of
  its first letter `c, st, a_u`, and the chain states lie in the range of `c`. The ranges are orthogonal, and
  `p_v + p_u = 1`.
- **(Avail).** `t_x s_y = 0` for `x ≠ y`, including on the chain. `t_x s_x` is the projection onto the vectors at which
  `x` is available.
- **(Cov).** Diagonal operators commute with range projections. On the domain of `x`, `t_x X s_x` acts by
  `X(xw) = σ_x(X)(w)`, and on the chain by the chain values.
- **Base ring.** All relations of the base ring hold pointwise.
- **(b) (Pos).** On `u`-vectors, `t_d e_N s_d` acts as `[L = 0]`, because `N(dη) = L(η)`. A `u`-vector is either a chain
  state (`L = k ≥ 1`) or begins with `a_u` (`L ≥ 1`), `st` or `c`.
  - For `st ξ`, `L = 0` forces `N(ξ) = 1`, and then `Δ = N(ξ) − 1 = 0`.
  - For `c w`: `L(cw) = 0` gives `L(w) = 0`, hence `Δ(w) = 0` by induction, so `c` is not available at `w`.

  So `[L=0] ≤ e_Δ` holds, and all the operators are diagonal, so they commute.

## 2. X_k ∈ R_abs, and it acts as 1 on the chain (author's (c))
- **`[Δ = i] = t_c^i e_Δ s_c^i`.** It acts as the indicator of `Δ = i`. If `Δ(η) = i ≥ 1`, the steps
  `Δ = i, …, 1` are all nonzero, so `c^i η` is legal and ends at `Δ = 0`. Otherwise either `s_c^i η = 0` or
  `Δ(c^i η) ≠ 0`. This holds in `M` and in the concrete model.
- **`[L = k] = t_d t_st [Δ = k−1] s_st s_d`.** Here `L(η) = N(dη)`, `st` is legal iff `N ≠ 0`, and
  `Δ(st ξ) = N(ξ) − 1`. So it acts as `[L = k]`.
- **On the chain.** `Δ(∅, n+i) = 1/2 − n − i ≠ 0`, so every `[Δ = i]` is `0` there, while `[L = k] = 1`. So
  `X_k e_(∅,n) = e_(∅,n)`.

## 3. X_k = 0 in the concrete model (author's (d))
- **Shape of a `u`-state.** With tail `b^∞`, every `u`-state is `(c | a_u)^* st ξ`. The `u`-segment is finite, because
  the tail has type `v`.
- **The capacity bound.** `Δ = L` right after the `st`. After that:
  - `c` keeps `L` and lowers `Δ` by one;
  - `a_u` raises both by one.

  So `L − Δ = #c ≥ 0`. Concrete availability of `c` (`Δ ≥ 1`) keeps `Δ ≥ 0`, and `Δ` is an integer.
- **Conclusion.** If `L = k` then `Δ ∈ {0, …, k}`, and the idempotents `[Δ = i]` sum to `[L=k]`. Hence `X_k = 0`.
  - The kernel is nonzero, because `X_k` acts on `M` as 1 on the chain.
  - The kernel is proper, because `R_conc ≠ 0`.
  - Dropping `a_u` changes nothing.

## 4. Non-blocking
- **The "Lesson" is heuristic.** Its general claims are useful design guidance, not proved in that generality:
  - that finitely many polynomial and idempotent relations "cannot enforce integrality of `Δ`";
  - that one unbounded register gives "no hidden identities".
- **Wording.** Say so, or phrase them as "for relations of this shape".
