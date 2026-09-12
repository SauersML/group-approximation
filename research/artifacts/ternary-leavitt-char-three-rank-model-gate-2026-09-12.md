# Characteristic-three rank models of the ternary Leavitt unit group

Lane `w3-gate-char3`, 2026-09-12. Supports `ternary-leavitt-rank-models-move-z-iff-nontrivial` and
the open gate `ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`.

## 0. Setup

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = −1`, `PG = G/<z>`, and `π : G -> PG` the quotient map.
- `ι(g) = s0 g t0 + s1 t1`, the corner embedding (`leavitt-units-embed-in-their-scalar-quotient`).
- A *rank model* of a group `H` is a homomorphism `σ : H -> M^x`, where
  `M = prod_ω M_(n_i)(k_i) / ker ρ` is a rank ultraproduct over fields `k_i` of characteristic three and
  `ρ = lim_ω rk / n_i`. It is *trivial* if `σ(H) = {1}`, *injective* if `ker σ = 1`.
- A rank model `σ` of `G` is *anti-central* if `σ(z) = −1`.
- The lane's question: does `G` have a rank model moving `z`? A yes refutes
  `ternary-anti-invariant-swap-corner-is-full` (`anti-central-rank-models-kill-ternary-corner-witnesses`
  with `Γ = G`).

## 1. Two lemmas

**Lemma 1.1 (normal subgroups).** Every normal subgroup `K` of `G` is `G` or lies in `<z>`.

*Proof.* `K<z>/<z>` is normal in `PG`, which is simple (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`,
`p = 3`). If it is trivial, `K <= <z>`. Otherwise `K<z> = G`. Since `z` is central,
`[G, G] = [K<z>, K<z>] = [K, K] <= K`, and `G` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`),
so `K = G`. QED

**Lemma 1.2 (tensor squares).** Let `k` be a field of characteristic not two.
- (a) For `A, A'` in `M_n(k)`, `rk(A⊗A − A'⊗A')/n^2 <= 2 rk(A − A')/n`. So `A -> A⊗A` descends to a
  multiplicative map from `prod_ω M_(n_i)(k_i)/ker ρ` to `prod_ω M_(n_i^2)(k_i)/ker ρ`, and a rank model
  `σ` gives a rank model `σ⊗σ`.
- (b) Let `A` be in `GL_n(k)` and `δ = rk(A⊗A − I)/n^2 < 1/3`. Then `rk(A − μ I)/n <= δ` for some
  `μ` in `{1, −1}`.
- (c) If a unit `u` of a rank ultraproduct satisfies `u⊗u = 1`, then `u = 1` or `u = −1`.

*Proof.*
- (a) `A⊗A − A'⊗A' = (A − A')⊗A + A'⊗(A − A')`, and `rk(X⊗Y) = rk(X) rk(Y) <= n rk(X)`.
  Multiplicativity holds on the nose at every stage.
- (b) Identify `k^n ⊗ k^n` with `M_n(k)` by `v⊗w -> v w^T`. Then `(A⊗A)X = A X A^T`, so
  `ker(A⊗A − I) = {X : A X = X B}` with `B = A^(−T)`. That is the space of `k[x]`-module maps from
  `(k^n, B)` to `(k^n, A)`, of dimension at least `(1 − δ) n^2`.
  - Over an algebraic closure its dimension is `Σ_ν Σ_(i,j) min(a_i(ν), b_j(ν))`, with `a_i(ν)` and
    `b_j(ν)` the Jordan block sizes of `A` and `B` at `ν`. Using `min(a_i, b_j) <= b_j`, it is at most
    `Σ_ν g(ν) m_B(ν)`, where `g(ν) = dim ker(A − ν)`. `B` has the Jordan types of `A^(−1)`, so
    `m_B(ν) = m(ν^(−1))`, the algebraic multiplicity of `ν^(−1)` in `A`.
  - So `(1 − δ) n^2 <= Σ_ν g(ν) m(ν^(−1)) <= n · max_ν g(ν)`. Let `ν*` maximize `g`. Then
    `rk(A − ν*) = n − g(ν*) <= δ n`.
  - If `ν* != ν*^(−1)`: `m(ν*^(−1)) <= n − m(ν*) <= δ n` and `Σ_(ν != ν*) g(ν) <= δ n`, so the sum is
    at most `n · δn + δn · n = 2δ n^2 < (1 − δ) n^2`. Contradiction. So `ν* = ±1`, which lies in `k`,
    and ranks over `k` equal ranks over the closure.
- (c) If `uv = 1` in `M`, representatives satisfy `rk(u_i v_i − I)/n_i -> 0`, so `u_i` has rank at least
  `n_i − rk(u_i v_i − I)`, and some invertible `u'_i` differs from `u_i` by at most that rank. Along `ω`,
  `rk(u'_i ⊗ u'_i − I)/n_i^2 -> 0`; (b) gives signs `μ_i` with `rk(u'_i − μ_i)/n_i -> 0`, and `μ_i` is
  `ω`-almost constant. QED

## 2. The theorem

**Theorem 2.1.** The following are equivalent.
1. `G` has a rank model `σ` with `σ(z) != 1`.
2. `G` has a nontrivial rank model.
3. `G` has an injective rank model.
4. `PG` has a nontrivial rank model.
5. `PG` has an injective rank model.
6. `G` has an anti-central rank model.

Explicitly: if `σ` is nontrivial, `σ∘ι` is injective and moves `z`. If `σ` is anti-central, `σ⊗σ`
factors through a nontrivial model of `PG`.

*Proof.*
- (2) ⟹ (3). By Lemma 1.1, `ker σ <= <z>`. Then `ker(σ∘ι) = ι^(−1)(ker σ) <= ι^(−1)(<z>) = {1}`,
  since `ι(G)` meets the scalars only in `1`.
- (3) ⟹ (1) and (6) ⟹ (1): `z != 1`.
- (1) ⟹ (6). `f = 2(1 − σ(z))` is an idempotent commuting with `σ(G)`, nonzero because `2` is
  invertible. The corner `fMf`, renormalized by `ρ(f)`, is again a rank ultraproduct over the same
  fields (as used in `matrix-unit-rank-models-extract-ring-rank-models`), and `g -> σ(g) f` is a model
  with `z -> −f`.
- (6) ⟹ (4). `T = σ⊗σ` is a rank model (Lemma 1.2(a)) with `T(z) = (−1)⊗(−1) = 1`, so it factors
  through `PG`. If `T` were trivial, Lemma 1.2(c) would give `σ(g) = μ(g)` in `{±1}` for all `g`. Then `μ`
  is a homomorphism `G -> {±1}`, trivial because `G` is perfect, so `σ(z) = 1`, contradicting
  `σ(z) = −1 != 1`.
- (4) ⟹ (5). `PG` is simple.
- (5) ⟹ (3). `σ∘π∘ι` is injective, because `π∘ι` is (`leavitt-units-embed-in-their-scalar-quotient`).
- (3) ⟹ (2). `G != 1`. QED

## 3. Consequences

**Corollary 3.1.** If `G` or `PG` has any nontrivial rank model in characteristic three, then
`ternary-anti-invariant-swap-corner-is-full` is false.

*Proof.* Theorem 2.1 gives a model of `G` moving `z`. Apply Theorem 2.1(d) of
`research/artifacts/ternary-corner-state-sources-2026-09-12.md` with `Γ = G`. QED

**Corollary 3.2 (the gate is one question).** The two directions of the lane's question are:
- yes: `G`, equivalently `PG`, has a nontrivial characteristic-three rank model, and the ternary corner dies;
- no: every characteristic-three rank model of `G` and of `PG` is trivial, so neither group is `F_3`-linear
  sofic, since a linear sofic approximation over `F_3` is an injective rank model.

"Moving `z`" is not an extra condition, and nothing is gained by separating `G` from `PG`.

**Remark 3.3 (comparison).** `projective-ternary-group-is-f3-linear-sofic` records that `F_3`-linear
soficity of `PG` kills the anti-central corner through stable finiteness. Theorem 2.1 needs no separation:
one nontrivial model of `PG`, or of `G`, suffices. It also adds the converse direction, from models of `G`
to models of `PG`, through tensor squares.

**Remark 3.4 (corner locality in characteristic three).** For a prefix `P`,
`ι_P(g) = S[P] g T[P] + (1 − S[P] T[P])` is an injective endomorphism with `ι_P(G)` not inside `<z>`. By
Lemma 1.1, `σ` is trivial exactly when `σ∘ι_P` is. The extraction step needs both odd-characteristic
identities `N_12^2 = 0` and `N_23 N_12 = 0` (`el3-unit-root-matrix-units-iff-two-root-identities`), then
`matrix-unit-rank-models-extract-ring-rank-models` and `leavitt-algebra-has-no-unital-rank-model`.
