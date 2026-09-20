---
rg: 2
id: past-conditioned-domination-locally-amenable-proof
kind: route
title: Apply the Huang-Xu-Yi Pinsker formula twice to get I(x_1; y_G | x_{<1}) = h(y) on amenable ordered hosts, then transport finite ordered patterns into nilpotent quotients of a central series
target: past-conditioned-domination-holds-on-locally-amenable-orders
requires: []
artifacts:
  - experiments/past-conditioned-domination-2026-09-17/hxy-1409.0275-excerpts.txt
  - experiments/past-conditioned-domination-2026-09-17/check_d_magnus_nilpotent.py
---

**Import.** W. Huang, L. Xu and Y. Yi, *Asymptotic pairs, stable sets and chaos in positive entropy systems*,
arXiv:1409.0275v1, read on 2026-09-19 from the arXiv PDF. The verbatim text is in the excerpts artifact.

- **Theorem 3.1.** "Let G be a countable discrete infinite amenable group with algebraic past Φ, (X, G) be a
  G-system, µ ∈ M(X, G), and A be a G-invariant sub-σ-algebra of B^µ_X. Then for any α, β ∈ P^µ_X,
  h_µ(G, α ∨ β|A) = h_µ(G, β|A) + H_µ(α|β_G ∨ α_Φ ∨ A), where β_G = ⋁_{g∈G} gβ and α_Φ = ⋁_{g∈Φ} gα. In
  particular, h_µ(G, α|A) = H_µ(α|α_Φ ∨ A)."
- **Algebraic past.** "Φ ∩ Φ^{-1} = ∅, Φ ∪ Φ^{-1} ∪ {e_G} = G, Φ · Φ ⊆ Φ", with "g_1 <_Φ g_2 if
  g_2^{-1} g_1 ∈ Φ". So `Φ = {g : g <_Φ e_G}`, and `<_Φ` is a left-invariant order.
- **Monotonicity.** "H_µ(α|A) increases with respect to α and decreases with respect to A".
- **Entropy of a partition.** `h_µ(G, α) = lim (1/|F_n|) H_µ(⋁_{g∈F_n} g^{-1}α)`, over a Følner sequence.

A nontrivial left-orderable group is torsion-free and hence infinite, so the hypothesis "infinite" is automatic.

**Step 1 (conventions).**
- Let `X = (A^k)^G` carry the left shift `(g·x)(h) = x(g^{-1}h)` and the uniform Bernoulli measure `µ`. This
  is a compact G-system.
- Let `α` be the partition by `x(1)`. Then `gα` is the partition by `x(g)`, so `α_Φ = σ(x(g) : g < 1)`, which
  is `x_{<1}`.
- Let `β` be the partition by `y_1 = psi(x(e))_(e∈E)`. Then `gβ` is the partition by
  `x ↦ psi((g^{-1}·x)(e))_e = psi(x(ge))_e = y_g`. So `β_G = σ(y_g : g ∈ G)`.

**Step 2 (Theorem 3.1 twice, with trivial A).**
- Order `(α, β)`: `h(α ∨ β) = h(β) + H(α | β_G ∨ α_Φ)`.
- Order `(β, α)`: `h(α ∨ β) = h(α) + H(β | α_G ∨ β_Φ) = h(α)`. The last step holds because `β` is
  measurable with respect to `⋁_{e∈E} eα ⊆ α_G`, so the conditional entropy is `0`.
- By the "in particular" clause and the independence of the coordinates,
  `h(α) = H(α | α_Φ) = H(α) = k log q`.
- Hence `H(α | α_Φ ∨ β_G) = H(α | α_Φ) - h(β)`, that is,
  `I(x_1 ; y_G | x_{<1}) := H(α|α_Φ) - H(α|α_Φ ∨ β_G) = h(β)`.
- Subadditivity of `H` over the join gives `H(⋁_{g∈F_n} g^{-1}β) <= |F_n| H(β)`, so `h(β) <= H(β) = H(y_1)`.

**Step 3 (finite F).**
- For finite `F`, monotonicity gives `H(α | α_Φ ∨ β_F) >= H(α | α_Φ ∨ β_G)`. So
  `I(x_1 ; y_F | x_{<1}) <= I(x_1 ; y_G | x_{<1}) = h(y) <= H(y_1)`.
- Conditioning on `x_{<1}` equals conditioning on `x_P`, where `P = FE ∩ Φ`, because the coordinates outside
  `FE ∪ {1}` are independent of `(x_1, x_P, y_F)`.
- This proves part 1 of the claim.

**Step 4 (transfer, part 2).**
- Let `φ: <E ∪ F> -> G'` be a homomorphism that is injective on `S = FE ∪ {1}` and preserves the sign of
  each site relative to `1`.
- `φ` is injective on `E`: if `φ(e) = φ(e')`, then for any `f ∈ F`, `φ(fe) = φ(fe')`, so `fe = fe'` and
  `e = e'`.
- `φ` is injective on `F` by the same argument.
- Put `E' = φ(E)` and `F' = φ(F)`, and transport `psi` along `φ|_E`. Then `φ(f)φ(e) = φ(fe)`, so
  `s ↦ φ(s)` is a bijection `S -> F'E' ∪ {1}`. It carries each window `fE` onto `φ(f)E'` with the same
  labels, and it carries the past sites `S ∩ Φ` onto `φ(S) ∩ Φ'`.
- The families `(x(s))_{s∈S}` and `(x'(φ(s)))` are both iid uniform. Under the bijection, `y_f`
  corresponds to `y'_{φ(f)}` and `x_P` to `x'_{P'}`.
- So `I(x_1; y_F | x_P) = I(x'_1; y'_{F'} | x'_{P'})`, which is at most `H(y'_1) = H(y_1)` by part 1 on
  `G'`.

**Step 5 (central-series orders, part 3).**
- **The rule is a bi-order.** For `g != 1`, the index `d` exists because `G_1 = G` and `∩ G_c = 1`.
  - Let `g ∈ G_d \ G_(d+1)` and `h ∈ G_e \ G_(e+1)` be positive, with `d <= e`.
  - If `d < e`, then `gh ≡ g mod G_(d+1)`.
  - If `d = e`, the image of `gh` is the sum of the two positive images, so it is nonzero and positive.
  - In both cases `gh > 1`.
  - Totality and antisymmetry hold because the image of `g^{-1}` is minus the image of `g`.
  - Conjugation fixes the image of `g`, because `G_d/G_(d+1)` is central in `G/G_(d+1)`.
- **The pattern embeds in a nilpotent quotient.** Take a finite `S ∋ 1`.
  - Choose `c` with `S^{-1}S ∩ G_(c+1) = {1}`. This is possible because the chain decreases and each
    nontrivial element eventually leaves it.
  - The quotient map `π: G -> N = G/G_(c+1)` is injective on `S`.
  - `N` is nilpotent, since the image series is central of length `c`, and hence amenable.
  - `N` carries the same rule, using the factors `G_d/G_(d+1)` for `d <= c`.
  - Every `s ∈ S \ {1}` lies outside `G_(c+1)`, so its index `d <= c` and its factor image are unchanged.
    So `π` preserves signs.
- Step 4 now applies.

**Step 6 (Magnus order, part 4).**
- Let `μ: F_n -> Z<<X_1..X_n>>^×` be given by `a_i ↦ 1 + X_i`.
- **The Magnus filtration is central.** Put `D_c = {w : μ(w) - 1 ∈ (deg >= c)}`.
  - This is a normal subgroup.
  - `μ(uv) - 1 = (μ(u) - 1) + (μ(v) - 1) + (μ(u) - 1)(μ(v) - 1)`, so the degree-`c` part `L_c` is a
    homomorphism `D_c -> Z^{monomials of degree c}`, with kernel `D_(c+1)`.
  - So `D_c/D_(c+1)` is torsion-free.
  - Normality: `μ(gwg^{-1}) - 1 = μ(g)(μ(w) - 1)μ(g)^{-1}`.
  - Centrality: write `μ(u) = 1 + U'` and `μ(v) = 1 + V`, with `U'` of degree `>= 1` and `V` of degree
    `>= c`. Then `μ(u^{-1}v^{-1}uv) - 1 = μ(u)^{-1}μ(v)^{-1}(U'V - VU')`, which has degree `>= c + 1`.
    So `[F_n, D_c] ⊆ D_(c+1)`.
- **The filtration separates points.** Let `w = a_{i_1}^{m_1} ... a_{i_r}^{m_r}` be a nontrivial reduced
  word, with `i_j != i_(j+1)` and `m_j != 0`.
  - `μ(a_i^m) = 1 + m X_i + X_i^2(...)`.
  - The monomial `X_{i_1} ... X_{i_r}` has no two equal adjacent letters. In the expansion, each selection
    of terms concatenates blocks `X_{i_j}^{b_j}`, with `b_j >= 1`, over the selected factors.
  - A block with `b_j >= 2` puts two equal letters side by side. So a selection that gives this monomial
    has every `b_j = 1`, and then its `r` letters need all `r` factors selected.
  - So the coefficient is `m_1 ... m_r != 0`, `μ(w) != 1`, and `∩ D_c = 1`.
- **The Magnus sign is the central-series rule.** Order each factor `L_c(D_c)` lexicographically by the
  first nonzero coefficient in lex order of monomials. The Magnus sign (first nonzero coefficient of
  `μ(w) - 1` in (degree, lex) order) is exactly the rule of Step 5 for this series.
- Part 3 applies.
- The script checks this numerically on the tested configurations: `separating_degree` and `trunc_sign`
  compare the degree-`c` truncation, which computes `F_2/D_(c+1)`, against the full sign.
