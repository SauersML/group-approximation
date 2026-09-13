# EX review, groups: part 7. L²-acyclicity of Leavitt units, amenable-orbit full groups, weak models of simple groups, Atiyah base change

Lane `ex-verify-groups`, 2026-09-13, ~01:10 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 7.1 ex-lueck-approximation: the frame chain (912ea9ef17, 078c7a7529). PASS, with a trust surface

- **`l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers`.**
  - The double complex `N(G) ⊗_ZG (P_* ⊗ C_*(X))`, with stabilizers fixing simplices pointwise.
  - Filtering by `p`, Shapiro gives `E^1_(p,t) = ⊕_[σ] H_t(G_σ; N(G))`. Its dimension is
    `β_t^(2)(G_σ)` by induction invariance.
  - Filtering by `t`, rows `1..m` vanish because `H̃_d(X) = 0` and `N(G)` is `Z`-flat. So
    `H_n(Tot) = H_n(G; N(G))` for `n <= m`.
  - Dimension additivity and cofinality over a finite filtration of countable sums finish.
- **`frame-acyclic-rings-have-low-degree-l2-acyclic-gl`.**
  - The stabilizer of a `k`-frame, `k <= r-1`, is conjugate to `J = {[[I_k, b],[0, d]]}`.
  - `U = ker(J -> GL_(r-k)) ≅ M_(k x (r-k))(A)` is infinite abelian normal, so `β_*^(2)(J) = 0` by Cheeger–Gromov.
  - Simplices in dimension `p <= r-3` carry `k <= r-2` vectors. The calibration `A = F_2` (finite, so
    `β_0^(2) != 0`) shows the hypothesis `A` infinite is needed.
- **`binary-leavitt-unit-group-is-l2-acyclic`.** At rank `r = n+3`, Khanh's Corollary 4.3 gives the
  `(r-3)`-acyclic frame complex. A complete prefix code gives the ring isomorphism `M_r(R) ≅ R`, so
  `GL_r(R) ≅ R^x`, and all L²-Betti numbers vanish.

Verdict PASS. Trust surface: Khanh arXiv:2609.08428v1 (Definition 2.1, Corollary 4.3) is an unrefereed v1
preprint, imported with a proof-chain read by the literature lane. This review did not re-read it.

## 7.2 ex-fp-simple-sofic: amenable-orbit full groups (1da285e701, ee5d106763, dc4793077f). PASS

- **`amenable-orbit-full-group-subgroups-are-sofic`.**
  - At free points the cocycle identity `c_gh(y) = c_g(hy) c_h(y)` holds, with `gy = y` iff `c_g(y) = 1`.
  - The partial maps `σ_g(λ, j) = (c_g(λ x_j) λ, j)` are injective by freeness.
  - On `λ ∈ Q` with `Eλ ⊆ Q`, `σ_g σ_h = σ_gh` exactly, since `E` contains the ranges of `c_g`, `c_h`, `c_gh`.
    So the defect is at most `β(Q)`.
  - Fixed points on the domain are exactly `λ x_j ∈ Fix g`. Means come from invariance, with Chebyshev and
    a union bound over `F`.
  - Tensor amplification gives separation `1 - (1-δ)^m`.
  - Credit is correctly left to folklore (Elek–Szabó, Elek).
- **`kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf`.**
  - On `Z = {(x,λ) : λx ∈ Y}` with `μ x counting`, the action `g.(x,λ) = (x, c_g(λx) λ)` preserves measure.
  - Følner indicators `ξ_Q` have `||ξ_Q||^2 = |Q| μ(Y)`. The boundary is `m(s.A_Q \ A_Q) <= |B_Q| μ(Y)`.
    The node's bound `2|B_Q|/(|Q| μ(Y))` is looser than needed; `2|B_Q|/|Q|` suffices. Either tends to `0`.
  - (T) gives a nonzero invariant `η`. Fibrewise it is square-summable and constant on infinite `Γ`-orbits,
    hence `0`. So almost every orbit is finite.
  - Residual finiteness follows from a positive-measure moved set of finite orbits. Credit is correctly
    left to Connes–Weiss and Schmidt.
- **Scope, correctly recorded.** This certificate cannot reach infinite simple Kazhdan groups. So
  `hyperlinear-fp-infinite-simple-group` stays open through this route, and computes open at `f79305e9c`.

## 7.3 ex-weak-soficity: `simple-group-support-and-semisimple-rank-models-collapse` (4656ff0c3d, 4e7e23aa0d). PASS

- **Support type.**
  - The moved set `Ω_0 = ∪ supp a_x` is invariant, and its complement is fixed.
  - Suppose relators have `|supp| < |Ω_0|/n`. Normalize on `Ω_0`. Some generator moves at least `1/|X|` of
    the points, so the ultraproduct homomorphism is nontrivial, hence injective by simplicity. Then `G` is
    sofic.
  - Subadditivity of `f` converts the constant `ε_0` into `ε >= 1/ceil(1/ε_0)`.
- **Rank type, any characteristic.**
  - `U = ∩ ker(a_x - 1)` and `dim V/U <= Σ rk(a_x - 1)`.
  - **Lemma 2.2, checked line by line.**
    - `a_x - 1 = [[0, N_x],[0, D_x]]`.
    - `a_x^-1` has lower block `(1+D)^-1` and corner `-N(1+D)^-1`. So `E'` has rank `<= 2ηM`.
    - `N̂_i N̂_j = 0`, and telescoping gives `w(a) = 1 + Σ e_(w,x) N̂_x + E_w` with `rk E_w <= 2 L_w η M`.
    - `H_1(G) = 0` writes each `e_x` as an integer combination of relator exponent vectors, which bounds
      `rk N̂_x`.
  - **Lemma 2.3.** Some generator keeps normalized rank `>= η/|X|` on `V/U`, while relators tend to `0`. The
    rank-metric ultraproduct homomorphism is injective by simplicity, so `G` is `F`-linear sofic.
  - **Item 4.** `rk(Ad g - 1) <= 2nρ`, and `dim C(g) = Σ_λ Σ_j (μ'_(λ,j))^2 <= n max_λ geo(λ)`, with
    `geo <= n - ρ` on `F` and `<= n/2` off `F`.

Verdict PASS. Consequence recorded correctly: support-type weak models of the Leavitt unit group do not
exist, and rank-type weak soficity over `F_q` equals `F_q`-linear soficity. `non-weakly-sofic-group-exists`
stays open.

## 7.4 ex-atiyah-torsion-free: `atiyah-base-change-holds-off-a-countable-set` (2353ca2aca). PASS at step level

The hypotheses are named: `G` torsion-free and Strong Atiyah over `Q̄`.
- `D = D_(Q̄[G])` is a skew field (Linnell's criterion import). `D[x]` with central `x` is Euclidean, which
  gives Jacobson normal form, and evaluation `x -> z` is a ring map into `U(G)`.
- So `dim ker A(z) = (n - r) + Σ dim ker(z - C_i)` for companion matrices over `D`.
- Eigenspaces of distinct eigenvalues are independent in `U(G)^(l_i)`. So only countably many `z` jump,
  over countably many families.
- Off `E_G`, nonzero `f ∈ D[x]` stay invertible at `z` (linear representation plus Schur complement). The
  Ore universal property embeds `D(x)` as the division closure of `Q̄(z)[G]`.
- The several-variable Borel, null and meagre statement was not re-derived.

`strong-atiyah-torsion-free` is correctly not claimed: algebraic extensions of `Q̄(z)` need
Jaikin-Zapirain–López-Álvarez Conjecture 3.
