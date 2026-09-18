# Referee report (gq-referee-a, proof-gap lens): the tracial harmonic ring, parts 1–3

**Reviewed:** parts 1–3 of `tracial-harmonic-ring-keeps-rational-scalars`, proved in steps (a)–(d) of
`tracial-harmonic-ring-keeps-rational-scalars-proof` (lane gq-deep-adelic-1, last touched 7b881b916). Read on
origin/main. Part 4 (Fuglede–Kadison) already has a gq-referee-b PASS and is outside this review.

**Verdict: PASS for parts 1–3.** No gaps found. Two facts are used silently and should be stated (§5).

Convention used throughout: `u g u^{-1} = g ∘ σ^{-1}`. So `u^k χ_D u^{-k} = χ_{σ^k D}` and
`u^{-k} f u^k = f ∘ σ^k`.

## 1. Setting
- **The `C_m` are nonempty.** An infinite minimal subshift has no isolated points (§5), so `U_k ∖ U_{k'}` is
  nonempty along a subsequence.
- **`f` is continuous.** At `x_∞` it is continuous because `f ≤ 1/m` near `x_∞`.
- **`f` is locally constant off `x_∞`.** Take `y ≠ x_∞`. It has a neighbourhood that avoids a neighbourhood
  of `x_∞`, and so meets only finitely many of the clopen `C_m`. Hence `f` is constant near `y`.

## 2. (a) Minimal tiling: `1/m ∈ R_h`
- **Clopen indicators.** Every clopen set is a finite disjoint union of cylinders, and cylinders are
  products of translates `u^{-t} χ_[a] u^t`. So `LC(X,Z) ⊆ R_h`, and `(1/m)χ_{C_m} = χ_{C_m} f ∈ R_h`.
- **Covering.** Minimality means every orbit meets `C_m`. So the translates `σ^k(C_m)` cover `X`, and by
  compactness finitely many do.
- **Disjoint tiles.** The `D'_i` are clopen, pairwise disjoint and cover `X`. Also `D_i = σ^{-k_i}(D'_i) ⊆ C_m`.
- **Assembly.**
  - `u^{k_i}(χ_{D_i} χ_{C_m} f)u^{-k_i} = (1/m) χ_{σ^{k_i}D_i} = (1/m) χ_{D'_i}`, since `f ≡ 1/m` on `D_i`.
  - Summing gives `(1/m)·1`.
- **Conclusion.** `1/m ∈ R_h` for every `m ≥ 1`, so `Q ⊆ R_h`. The element lies in `B`, because `B` is
  `σ`-invariant.

## 3. (b) Skew Laurent structure
- **`⊕_j B u^j` is a ring.** `(a u^j)(b u^k) = a (b∘σ^{-j}) u^{j+k}`, and `B` is `σ`-invariant, so the
  sum is closed under products.
- **It equals `R_h`.** It contains the generators, namely `u^{±1}`, the `χ_[a]` and `f`. Conversely
  `B ⊆ R_h`, by §2 and `f∘σ^k = u^{-k} f u^k`.
- **The sum is direct.** The canonical expectation satisfies `E(g u^k) = 0` for `k ≠ 0`, so the coefficient
  of `u^j` is `E(x u^{-j})`. Correct.
- **Elements of `B` are locally constant off a finite set.** Each element of `B` is a polynomial in finitely
  many generators.
  - The functions in `LC(X,Z)` are locally constant everywhere.
  - `f∘σ^k` is locally constant off the single point `σ^{-k}x_∞`.
  - Sums and products are therefore locally constant off a finite union of such points.
- **`B` contains `LC(X,Q)`.** It contains `Q` and `LC(X,Z)`. `B ⊆ C(X,Q)` because every generator is
  `Q`-valued.

## 4. (c) Simplicity and (d) centre
**(c) Simplicity.**
- **A nonzero diagonal coefficient.** Right multiplication by `u^{-j_0}` stays inside `I` and makes
  `a_0 ≠ 0`.
- **A good point `y`.**
  - `a_0` is continuous and nonzero, so it is nonzero on a nonempty open set.
  - That open set is infinite, since there are no isolated points, so it contains some `y ∉ F`.
- **A good neighbourhood `W`.**
  - `a_0` is constant on a neighbourhood of `y`, because `y ∉ F`. Its value `r = a_0(y)` lies in `Q^x`.
  - `σ^j y ≠ y` for the finitely many `j ∈ J∖{0}`, because there are no periodic points. So a small clopen
    `W ∋ y` has `σ^j W ∩ W = ∅` for all those `j`, by continuity and Hausdorffness.
- **Compression.** `χ_W x χ_W = Σ_j χ_W a_j χ_{σ^j W} u^j = r χ_W`. So `χ_W = r^{-1} χ_W x χ_W ∈ I`.
- **Tiling.** Tiling by clopen `D_i ⊆ W`, as in §2, gives `1 = Σ u^{k_i} χ_{D_i} χ_W u^{-k_i} ∈ I`. Correct.
- **Redundant condition.** The requirement `W ∩ F = ∅` is harmless, but only constancy of `a_0` on `W` is used.

**(d) Centre.**
- **Off-diagonal coefficients vanish.** Directness of the sum turns `zχ_W = χ_W z` into
  `a_j χ_{σ^j W} = χ_W a_j`.
  - `y ∈ σ^j W` holds iff `σ^{-j} y ∈ W`. Choosing `W ∋ y` with `σ^{-j}y ∉ W` gives `a_j(y) = 0` for `j ≠ 0`.
- **The diagonal coefficient is constant.** `uz = zu` gives `a_0∘σ^{-1} = a_0`.
  - The level sets of a continuous invariant function are closed and invariant, so by minimality `a_0` is
    constant. Its value lies in `Q`.
- **Conclusion.** `Z(R_h) = Q`. Correct.

## 5. Facts used silently (state them in the proof)
- **No isolated points.** An infinite minimal system has no isolated points. The set of isolated points is
  open and invariant. By minimality it is empty or all of `X`, and if it were all of `X`, compactness would
  make `X` finite. This fact is used for the nonemptiness of the `C_m`, and for choosing `y ∉ F` in (c).
- **No periodic points.** An infinite minimal system has no periodic points, because a periodic orbit is a
  closed invariant set. The node states this; it is used in (c) and (d).

## 6. Scope
- **Part 5** relies on `q-algebra-elementary-quotients-contain-gl-n-q`, which I have not reviewed, and on the
  standard fact that the centralizer of `E_N(R)` in `GL_N(R)`, for `N ≥ 3`, is `Z(R)^x·I`. With (d) and (e)
  that gives `Z(E_N(R_h)) ⊆ {±I}`. That step is correct.
- **This is not a host.** As the node says, `laurent-rational-symbols-block-fp-elementary-groups` shows that
  neither `E_N(R_h)` nor `PE_N(R_h)` is finitely presented. Simplicity of `PE_N(R_h)` is not claimed.
