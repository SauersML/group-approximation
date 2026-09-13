# The congruence-projection route to (H1) for the Theorem E vertex

Lane `nh-h1-theorem-e-instance`, swarm 7, 2026-09-12. Read at `83204067f`, rechecked at `94f11d0bd`.

## 1. Setting and verdict

- `R_+ = F_q[x_1..x_d]`, `L = F_q[x^(±1)]`, `r, d >= 3`.
- `Γ = EL_r(R_+) < Δ = EL_r(L) < G = Δ ⋊ SL_d(Z)`, the Kun–Thom Theorem E pair.
- `M = ∏_U M_n` with trace `τ = lim_U tr_n`. `σ : G -> U(M)` is trace-preserving: `τ∘σ = δ_e`.
- `σ_n(g) ∈ U(n)` are unitary representatives. For every fixed word, products of representatives converge in
  `||·||_2` to the representative of the product along `U`.
- For a finite-index ideal `I ⊆ R_+`, `Γ(I) = ker(Γ -> GL_r(R_+/I))` is the principal congruence kernel. It
  contains `e_12(I) ≅ (I, +)`, which is infinite, so `Γ(I)` is an infinite finite-index subgroup of `Γ`.
- (H1) is `hs-stable-vertex-rounding-for-every-model`: genuine `π_n : Γ -> U(n')`, `n'/n -> 1`, with
  `max_(s ∈ F) ||σ_n(s) - π_n(s)||_2 -> 0` along `U`.

**Candidate route.**
1. Take almost-invariant vectors of the congruence kernels.
2. Project onto their fixed subspaces.
3. Correct with the Kazhdan projection of `Γ(I)`.
4. Obtain genuine representations through the finite quotients `Γ/Γ(I)`.

**Verdict: obstruction, not a proof.**
- At the regular trace every fixed-level step of the route has asymptotically zero mass (Theorem 1).
- The route proves (H1) exactly for models with purely profinite vertex restriction, and there are none
  (Corollary 2).
- Any surviving version must work at levels `I_n` that escape every fixed ideal, on words of unbounded length
  (Proposition 3).
- Extendability to `G` shortens the normal generators of a level to logarithmic length. It does not shorten
  the averaging a projection needs, whose length is at least the dimension of the level (Remark 4).
- No proof of (H1), and no equivalence with a known-hard statement, is obtained.

## 2. The regular trace kills fixed levels

**Theorem 1.** Let `σ : G -> U(M)` satisfy `τ∘σ|Γ = δ_e`. Only this is used.

(a) **Exact fixed vectors.** For every infinite subgroup `K ≤ Γ`, let `p_K` be the largest projection
`p ∈ M` with `σ(k)p = p` for all `k ∈ K`. Then `τ(p_K) = 0`. In coordinates: let `k_1..k_m ∈ Γ` be distinct,
`ε < 1`, and let `p_n` be projections with `||σ_n(k_i)p_n - p_n||_2 <= ε ||p_n||_2` for all `i`. Then

```text
lim_U tr(p_n)  <=  1 / (m (1 - ε)^2).
```

(b) **Almost-invariant mass.** Let `S ⊂ Γ` be finite and symmetric, and let `κ > 0` be such that
`max_(s∈S) ||λ_Γ(s)ξ - ξ|| >= κ ||ξ||` for every `ξ ∈ ℓ^2(Γ)`. For `S = F_I` with `(F_I, κ_I)` a Kazhdan pair of
`Γ(I)`, `κ = κ_I` works, because `λ_Γ|Γ(I)` is a multiple of `λ_(Γ(I))`, which has no invariant vectors. Let
`V_n ⊆ C^n` be subspaces with `max_(s∈S) ||σ_n(s)v - v|| <= ε||v||` for all `v ∈ V_n`. If `ε < κ/√|S|`, then
`lim_U dim V_n / n = 0`.

(c) **Roundings are asymptotically regular and have unbounded level.** Let `π_n` be (H1) roundings of `σ|Γ`. Then:
- `lim_U tr_(n') π_n(g) = δ_e(g)` for every `g ∈ Γ`;
- for every `g ≠ e`, `{n : π_n(g) = 1} ∉ U`;
- for every finite-index ideal `I`, the projection `P_(n,I)` onto the `π_n(Γ(I))`-fixed vectors satisfies
  `lim_U tr P_(n,I) = 0`.

In particular the root ideals `I_n = {f : π_n(e_12(f)) = 1}` satisfy `{n : f ∈ I_n} ∉ U` for every `f ≠ 0`. So
`I_n` escapes every fixed nonzero element, and hence every fixed finite-index ideal.

*Proof of (a).*
- Take distinct `k_1..k_m ∈ K` and put `A = (1/m) Σ σ(k_i)`. Then
  `||A||_2^2 = (1/m^2) Σ_(i,j) τ(σ(k_i^(-1) k_j)) = 1/m`, since only the `m` diagonal terms survive.
- `σ(k_i)p_K = p_K` gives `τ(p_K) = τ(A p_K) <= ||A||_2 ||p_K||_2 = m^(-1/2) τ(p_K)^(1/2)`.
- So `τ(p_K) <= 1/m`. Since `K` is infinite, `m` is arbitrary.
- Coordinates:
  - Put `A_n = (1/m) Σ σ_n(k_i)`. Then `||A_n||_2^2 -> 1/m` along `U`, uniformly in `p_n`, because each
    `σ_n(k_i)^* σ_n(k_j)` converges in trace to `σ(k_i^(-1) k_j)`.
  - `|tr((1 - σ_n(k_i)) p_n)| = |tr((1 - σ_n(k_i)) p_n · p_n)| <= ε tr(p_n)`.
  - So `tr(p_n) <= |tr(A_n p_n)| + ε tr(p_n) <= ||A_n||_2 tr(p_n)^(1/2) + ε tr(p_n)`.
  - Rearranging and taking `lim_U` gives the bound.

*Proof of (b).*
- Put `T_n = (1/(2|S|)) Σ_(s∈S) (σ_n(s) + σ_n(s)^*)`, and let `T` be the same expression in `M`.
- **Moments.** `τ(T^k)` expands into `τ∘σ` of fixed words in `S`, so `τ(T^k) = τ_(L(Γ))(λ(T)^k)`, where `λ(T)` is the
  same expression in `λ_Γ`. Both spectral measures live on `[-1, 1]`, so they coincide.
- **Spectrum of `λ(T)`.** For unit `ξ`, `1 - <λ(T)ξ, ξ> = (1/(2|S|)) Σ ||λ(s)ξ - ξ||^2 >= κ^2/(2|S|)`. So
  `spec λ(T) ⊆ [-1, 1 - κ^2/(2|S|)]`.
- **Passage to coordinates.** `lim_U tr T_n^k = τ(T^k)`. By Weierstrass on `[-1, 1]`, `lim_U tr f(T_n) = τ(f(T))` for
  continuous `f`.
- **Cutoff.** Put `c = 1 - κ^2/(2|S|)` and fix `η > 0`. Take continuous `0 <= f <= 1` with `f = 1` on
  `[c + η, 1]` and `f = 0` on `[-1, c + η/2]`. Then `lim_U tr 1_([c+η, 1])(T_n) <= τ(f(λ(T))) = 0`.
- **Min-max.** For unit `v ∈ V_n`, `<T_n v, v> = 1 - (1/(2|S|)) Σ ||σ_n(s)v - v||^2 >= 1 - ε^2/2`. By min-max, `T_n`
  has at least `dim V_n` eigenvalues `>= 1 - ε^2/2`.
- **Conclusion.** `ε < κ/√|S|` gives `1 - ε^2/2 > c`. Take `η < 1 - ε^2/2 - c`.

*Proof of (c).*
- Each `g ∈ Γ` is a fixed word in `F`. So `||σ_n(g) - π_n(g)||_2 -> 0` along `U`, after the `o(n)` padding, which
  changes normalized traces by `o(1)`.
- Hence `tr π_n(g) - tr σ_n(g) -> 0`, and `tr σ_n(g) -> δ_e(g)`.
- If `π_n(g) = 1` for `U`-many `n` with `g ≠ e`, then `tr π_n(g) = 1` on a `U`-large set, a contradiction.
- `P_(n,I)` is a genuine projection with `π_n(k)P_(n,I) = P_(n,I)` for all `k ∈ Γ(I)`. Run the coordinate argument
  of (a) with `π_n` in place of `σ_n`, `ε = 0`, and `m` distinct elements of `e_12(I)`. This uses only
  `tr π_n(k_i^(-1) k_j) -> δ_(ij)`. It gives `lim_U tr P_(n,I) <= 1/m` for every `m`. ∎

**Relation to the corpus.**
- Item 3 of `laurent-extension-agrees-iff-inverse-defects-commute` is the special case `g = e_12(x_i^(m!) - 1)` of
  (c): the unit order of `x_i` is `U`-unbounded.
- §5 of `nh-h1-quantitative-2026-09-12.md` shows that regular-trace models can be manufactured by tensoring with
  `λ_(Q_k)`. (c) is the converse constraint on the roundings themselves.

## 3. What the route can and cannot do

**Corollary 2 (the profinite projection).**
- Put `p_prof = ∨_I p_(Γ(I))`, the supremum over the countably many finite-index ideals.
- (i) At the regular trace, `τ(p_prof) <= Σ_I τ(p_(Γ(I))) = 0` by Theorem 1(a).
- (ii) For an arbitrary `σ : Γ -> U(M)`, not necessarily trace-preserving, `τ(p_prof) = 1` implies (H1) for `σ`.

So the fixed-subspace step proves (H1) exactly for models whose vertex restriction is purely profinite. At
the trace (H1) requires, that class is empty.

*Proof of (ii).*
- `p_(Γ(I))` increases along the directed set of ideals, since `I ⊆ J` gives `Γ(I) ⊆ Γ(J)`. So
  `τ(p_(Γ(I))) -> 1`.
- Each `p_(Γ(I))` commutes with `σ(Γ)`, because `Γ(I)` is normal. On `p_(Γ(I)) M p_(Γ(I)) ≅ ∏_U M_(k_n)`, `σ` is an exact
  representation of the finite group `Γ/Γ(I)`.
- Finite groups are HS-stable, and projections lift to coordinate projections of the same limit trace. So there
  are genuine coordinate representations of `Γ/Γ(I)` on `k_n`-dimensional corners, close on `F`.
- Pad the complement with the trivial representation. The defect on `F` is `<= 2(1 - τ(p_(Γ(I))))^(1/2) + o(1)`.
- A diagonal choice of `I = I(n)` along `U` gives `n' = n`. ∎

**Proposition 3 (where content could live).** Suppose the route yields genuine `π_n` through `Γ/Γ(I_n)` that
round `σ|Γ`. Then:
1. For every `f ≠ 0` in `R_+`, `{n : f ∈ I_n} ∉ U`. So the levels escape every fixed nonzero element, and hence
   every fixed finite-index ideal.
2. The injectivity radius `ρ_n = min{|g|_F : e ≠ g ∈ Γ(I_n)}` tends to `∞` along `U`. Every generating set of
   `Γ(I_n)`, in particular every Kazhdan set used to correct at level `I_n`, consists of words of `F`-length
   `>= ρ_n`.
3. A Kazhdan pair `(F_(I_n), κ_(I_n))` corrects a vector only if its defect on `F_(I_n)` is `< κ_(I_n)`.
   - The (H1) defect on a word of length `ℓ` is bounded only by `ℓ` times the defect on `F`, and the models
     give no rate on `F`.
   - The constants `κ_(I_n)` are not uniform in `n`: `uniform-kazhdan-fails-for-linear-theorem-e-pair`, and
     `|F_(I_n)| -> ∞` with the index.

*Proof.*
- Item 1 is Theorem 1(c), because `ker π_n ⊇ Γ(I_n)`.
- For item 2: the ball `B_F(ρ)` is finite. Each `g ≠ e` in it lies in `Γ(I_n) ⊆ ker π_n` only for `U`-null many
  `n`, by Theorem 1(c). So `B_F(ρ) ∩ Γ(I_n) = {e}` on a `U`-large set.
- Item 3 is the standard Kazhdan-projection estimate. ∎

**Remark 4 (depth/diameter mismatch; the one place extendability enters).** Take the level
`I_m = (x_1^m, ..., x_d^m)`, so `|R_+/I_m| = q^(m^d)`.
- **Normal generators are logarithmically short in `G`.**
  - `Γ(I_m) ⊇ E(r, R_+, I_m)`, and `E(r, R_+, I_m)` is normally generated in `Γ` by the `d·r(r-1)` elements
    `e_ij(x_k^m)`, since `e_ij(x_k^m g) = [e_il(x_k^m), e_lj(g)]`.
  - Their `F`-length in `Γ` is `>= m / D_F`, where `D_F` bounds the degrees of the entries of `F`, because a
    word of length `ℓ` has entries of degree `<= ℓ D_F`.
  - Their length in `G` is `O(log m)`: `SL_d(Z)` moves exponents, and unipotents of `SL_d(Z)`, `d >= 3`, are
    exponentially distorted (Lubotzky–Mozes–Raghunathan; standard, not re-verified here).
  - This is the scale that compressor transport controls, and it matches `D_n <= log_q n'`
    (`root-character-nonunit-depth-at-most-log-q-dimension`).
- **A projection needs long averages.**
  - A genuine representation through `Γ/Γ(I_m)` is determined by averaging over the quotient, not by the normal
    generators.
  - `|Γ/Γ(I_m)| >= |e_12(R_+/I_m)| = q^(m^d)`. A ball of radius `ρ` in `G` has at most `(2|F_G| + 1)^ρ` elements.
  - So any set of coset representatives contains elements of `G`-length `>= m^d log q / log(2|F_G| + 1)`.
- **Mismatch.** Extendability buys `O(log m)` on the relators and nothing on the averages, which need `≳ m^d`.
  This is the precise sense in which transport "exactifies an assumed rounding but does not produce one"
  (`hs-stable-vertex-rounding-for-every-model`, Attempts).
- **Status.** The counting lower bound is proved. The `O(log m)` upper bound is imported. Neither is used in
  Theorem 1 or Proposition 3.

## 4. Equivalence with a known-hard statement: not obtained

- **Restricted to wreath models.** (H1) at the models the endgame consumes holds vacuously if `W` is
  non-hyperlinear (quantitative artifact §5). Its equivalence with non-hyperlinearity is the unproved converse
  recorded in the (H1) Attempts.
- **Extension from `Γ`-models to `G`-models is not automatic.**
  - A regular-trace `Γ`-model need not extend: `G` has property (T) through `SL_d(Z)` and `Δ`, so there is no
    Følner averaging over `G/Γ` to build an extension.
  - So (H1) is not visibly equivalent to flexible HS stability of `Γ`, which is open (Dogon), and Becker–Lubotzky
    excludes only the strict form.

## 5. Status

- **Established here, unconditional:** Theorem 1(a), (b), Corollary 2.
- **Established under (H1):** Theorem 1(c) and Proposition 3.
- **Recorded as claim** `theorem-e-congruence-projections-vanish-at-regular-trace`, route `-proof`.
- **(H1) stays OPEN.** The candidate route is void at every fixed level. It can only work at escaping levels
  with non-uniform Kazhdan data on words of unbounded length.
- **Not pursued:** the Schur-multiplier firewall for Dogon's twisted sector. Its `K_2` stability inputs were
  not re-verified from sources.
