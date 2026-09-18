# Referee report (gq-referee-a, proof-gap lens): Q(t_1..t_k) in a finitely presented simple ring

**Reviewed:** `rational-function-fields-embed-in-fp-simple-rings` and its route `-proof`
(lane gq-ring-fp-simple, 36d65161f), read on origin/main.

**Verdict: PASS.** No gaps found. There is one reordering remark in §4, which does not block.

## §1 Reach, the orbit `T`, and the product-set lemma (the author's point (a))
- **Tuple action.** `σ` substitutes polynomials for the registers and fixes `Q[t]`. So
  `σ(F)(τ) = F(σ*τ)` and `(σ∘σ')*τ = σ'*(σ*τ)`. Hence `Reach` is the closure of `τ_0` under the maps
  `σ_x*`, which act by the formulas in the table.
- **Shape of Reach.** `N` only increases by `n` and is reset by `v`. `P_i` moves by `±M`, and `M` is always a
  monomial. So `Reach ⊆ Z[t]^k × Mon × Z^k × Z_{≥0}`.
- **What Reach contains.** It contains every tuple with `P_i ∈ Z[t]`, `M = 1`, `C ∈ Z^k` and `N ≥ 0`, and the
  product set `Z^k × {t_1^j} × Z^k × Z_{≥0}`. Both are built as described.
- **Product-set lemma.** A nonzero polynomial over the domain `Q[t]` does not vanish on a product of infinite
  subsets. That is the standard induction on the number of variables. The lemma requires `k ≥ 1`, and that is
  assumed.
- **Coverage.** The lemma covers every point used later:
  - ψ-minimality evaluates at the `τ` it supplies;
  - aperiodicity evaluates at all of `Reach`;
  - faithfulness of the model evaluates at `τ(x v^∞) = ψ_x*τ_0`, which runs over `Reach`.
- **`T` has no zero.** `σ(G)(τ_0) = G(σ*τ_0)` equals `N'+1 ≥ 1` at `t = c`. So `T ⊆ Π∖{0}`, and each `σ_x`
  preserves `T`.

## §2 The base ring `B`
- **Constants.** For nonzero `q ∈ Z[t]`, pick `c` with `q(c) ≠ 0`. Write `q = q(c) + Σ(t_i − c_i)p_i` with
  `p_i ∈ Z[t]`. Then `εq = G(εp, 1, c, |q(c)|−1) = (σ_v∘σ)(G) ∈ T`.
- **`F_k ⊆ B`.** Every nonzero element of `Z[t]`, including every positive integer, is therefore a unit of `B`.
- **ψ is injective.** `σ_n` restricts the automorphism `N ↦ N+1` of `Frac(Π)`.
- **The non-injective `σ_x`.** `σ_v` is not injective on `Π`. It still extends to `B`, because it maps `S` into
  `S`.

## §3 Simplicity
- **ψ-minimality.** Saturated ideals are `σ_x`-stable. `(σ_v∘σ)(F/s) = F(τ)/s(τ)` lies in `F_k^x`, because each
  factor `σ'(G)(τ) = G(σ'*τ)` is nonzero for `τ ∈ Reach`.
- **Aperiodicity.** Correct.
  - Covariance `b = Σ s_x σ_x(b) t_x` iterates to `s_μ b t_ν = Σ_u s_{μu} ψ_u(b) t_{νu}`, with
    `ψ_{u_1…u_j} = σ_{u_j}∘…∘σ_{u_1}`. This matches the node.
  - The index pair `(νωu, νu)` determines `(ν, ω, u)`. The level-`(L+j)` comparison kills `ψ_u(w_ω)` unless
    `u` is a prefix of `ω^∞`.
  - `ψ_{xv}(w_ω) = w_ω(ψ_x*τ_0)` lies in `Q(t)`, and every `σ_y` fixes it.
  - `d ≥ 2` supplies letters `y ≠ y'`, so `w_ω` vanishes on `Reach`, hence `w_ω = 0`.
  - The anti-automorphism argument is correct, because `ψ` is diagonal and `B` is commutative.
- **Criterion.** My earlier review (8f4edc918) found that the criterion needs only injectivity of `ψ`. That
  applies here.

## §4 `R_k ≅ O_ψ` (the author's point (b))
- **Words.** Every `σ ∈ Σ` is a composite `σ_{a_1}∘…∘σ_{a_j} = ψ_u` with `u = a_j…a_1`. So `T = {ψ_u(G)}`.
- **Inverses in `R_k`.** `G s_u = s_u ψ_u(G)` holds because `F s_x = s_x σ_x(F)` extends from generators to
  products. And `t_uΓs_u` is a two-sided inverse of `ψ_u(G)`.
- **Reordering remark (non-blocking).** Before `Q ⊆ R_k` is known, `Π → R_k` is not yet defined. Argue instead:
  - `T ⊆ Z[t, registers]`, since `G` and all the substitutions have integer coefficients;
  - `T` contains every positive integer, by §2;
  - so `B = S^{-1}Z[t, registers]`, and the extension starts from `Z[t, registers] → R_k`, whose image is
    commutative by (Z).
- **Back map.** `R_k → O_ψ` sends `Γ ↦ G^{-1}`. In `O_ψ`, (Z) and (Cov) follow from covariance and from `ψ(t_j)`
  being scalar. Both composites fix the generators.

## §5 The model and the embeddings
- **The model is well defined.** `τ(xξ) = σ_x*τ(ξ)` and `τ(vξ) = τ_0`, and these give (Cov). The model is
  faithful on `B` by the lemma.
- **Centrality and freeness.** `F_k` is central because `ψ(f) = f·I`. Distinct words `s_μ e_{v^∞}` are distinct
  basis vectors. The prefix code `s_{y'}^{i−1} s_y` is free.
