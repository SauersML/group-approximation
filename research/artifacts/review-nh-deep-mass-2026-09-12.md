# Review: deep non-unit root mass vanishes under vertex rounding (2026-09-12)

Lane `nh-deep-mass-reviewer`, swarm 6. Read at tip `6d29d4abc`.
- **Target:** `vertex-rounding-deep-nonunit-root-mass-vanishes`, ESTABLISHED in efe6ca919.
- **Route:** `deep-nonunit-root-mass-two-attractor-proof` (3396c3df5).
- **Artifact:** `research/artifacts/nh-deep-mass-2026-09-12.md` (1b4245549, 66253a5d8).

## Verdict: PASS

The route correctly derives `μ_n(depth_nu > 1) -> 0` along `U`, with no rate, from its four premises. I found no error, no gap and no hidden hypothesis; §5 has only non-blocking notes. All four premises already had PASS verdicts (§4). `review-backlog-4` is re-reviewing the premise proofs separately, in `review-backlog-4-2026-09-12.md`.

**Consequence, unchanged by this review:** with this claim, `theorem-e-vertex-unit-type-via-deep-root-mass` is open only through (H1) = `hs-stable-vertex-rounding-for-every-model`.

## 1. Lemma 1 (unit scaling): PASS

- **Finite image.** `π_n`, pulled back to `St_r(R_+)`, factors through `St_r(B_n)`, `B_n = R_+/I_n` finite. This is item 1 of the second premise, which holds under (H1) alone; see §4.
- **The identity.** In `St_r(B)`, `r >= 3`, with `u ∈ B^×` and `h_ij(u) = w_ij(u) w_ij(-1)`, Milnor's relations `w_ij(u) x_jk(v) w_ij(u)^(-1) = x_ik(uv)` and `w_ij(u) x_ik(v) w_ij(u)^(-1) = x_jk(-u^(-1) v)` (i, j, k distinct) give:

  ```text
  w_31(-1) x_12(f) w_31(-1)^(-1) = x_32(-f),    w_31(u) x_32(-f) w_31(u)^(-1) = x_12(u^(-1) f),
  so  h_31(u) x_12(f) h_31(u)^(-1) = x_12(u^(-1) f).
  ```

  The artifact writes `u^(±1)`, and the sign of the exponent is immaterial. The relation holds in `St_r` of any ring, so no `K_2` or centre issue arises: conjugation happens by the fixed unitary `π̃_n(h_31(u))`.
- **Surjectivity.** `St_r(R_+) -> St_r(B_n)` is onto, so `π̃_n(St_r(B_n)) = π_n(Γ)`, and `f -> π_n(e_12(u^(-1) f))` is unitarily conjugate to `f -> π_n(e_12(f))`. Hence `μ_n` is invariant under `χ -> χ(u ·)`.
- **Disintegration.** `U_0 = {1} × A_0^×` is a finite group of units, and `μ_n` is `U_0`-invariant, so `μ_n = ∫ Unif(U_0·χ) dμ_n`. `Sh`, `e_i` and `depth_nu` are `U_0`-invariant because `u x^a A_0 = x^a A_0`.
- **Source.** I did not re-read Milnor §9. The relations above are the standard Steinberg-group ones, re-derived here.

## 2. Lemmas 2 and 3: PASS

- **2(a).** `φ_M(x^(cw) R_+) = x^(cMw) φ_M(R_+) ⊆ x^(cMw) R_+`. Correct.
- **2(b), the event.** `c w ∉ Sh(D_M χ_0(u·))` iff `λ_0(u x^(cMw + Mb)) = 0` for all `b`, because `φ_M(R_+)` is spanned by the `x^(Mb)`. So the event is `u ∈ ker Λ` for an `F_q`-linear `Λ` on `A_0`.
- **2(b), independence.** The functionals `u -> λ_0(u h_j)`, `h_j = x^(cMw) y^j`, `y = x^(Mw)`, `j <= ℓ` (i.e. `b = jw`), are linearly independent.
  - A relation gives `g = h_(j_0)(α_(j_0) + y s) ∈ J(χ_0)`.
  - `R_+/J(χ_0)` is a quotient of the local ring `A_0`, so it is local, and `y ∈ m_0` is nilpotent there.
  - So the second factor is a unit, and `x^((c+j_0)Mw) ∈ J(χ_0)`.
  - Monomials outside `J(χ_0)` are exactly `Sh`, since `J` is the largest ideal in `ker λ_0`. So `(c+j_0)Mw ∉ Sh`, contradicting down-closedness and `(c+ℓ)Mw ∈ Sh`.
- **2(b), the count.** `P_(A_0)(ker Λ) = q^(-rank Λ) <= q^(-(ℓ+1))`. Conditioning on units costs `|A_0|/|A_0^×| = q/(q-1) <= 2`, since the residue field at `m_0` is `F_q`.
- **Lemma 3, setting.** `A` is positive, so its Perron root is simple and `θ = λ_2/λ_1 < 1`; the entrywise sandwich then follows from `A^k = λ^k(v ℓ^T + E_k)`.
- **Lemma 3, the scale.** `{t : ⌊tv⌋ ∈ Sh} = [0, s)`: `Sh` is finite and down-closed and `t -> ⌊tv⌋` is right-continuous, so the sup is not attained. `s >= depth`, since `⌊tv⌋ <= ⌊t⌋·1`.
- **Lemma 3, the bounds.** Both are correct by down-closedness. Implicitly `γ_k < 1`, which the choice of `k` guarantees.

## 3. Parameters, landing in `E_±`, counting, uniformity: PASS

- **`c_i - L >= 0`.** `-log(1-ε) < β/4` forces `ε < 1`, i.e. `K > (L+1)(1+γ_k)Λ max ℓ`. Then `c_i >= s/((1+γ_k)ℓ_iΛ) - 1 > L`.
- **Lower bound.** `c_i - L >= (1-ε) s/((1+γ_k)ℓ_iΛ)` needs `(L+1)(1+γ_k)ℓ_iΛ/s <= ε`, which holds because `s >= K`.
- **Ratio.** `ρ >= β - log((1+γ_k)/(1-γ_k)) + log(1-ε) > β/2`. The scale `s` cancels between `i = 1` and `i = d`.
  - Note: for `M_- = B^k`, `s` must be taken with `v_B = P v_A`. It still satisfies `s >= depth`, so the text "the same holds" is fine.
- **Depth event.** `c^(1) >= ⌊(K-1)/N⌋`, because `c M 1 <= cN·1 <= (K-1)·1 ∈ Sh`, and `c^(1) - L >= 0` since `K' >= 2`. So `depth_nu(D_M χ) >= K'` and `e_1, e_d >= K'-1 >= 1`.
- **Types under `φ_M`.**
  - `φ_M(m_0) ⊆ m_0` gives `m_0^N ⊆ φ_M^(-1)(I_0)`, so origin characters stay origin characters.
  - Unit type is preserved: a finite subring element that becomes a unit in an overring is a non-zero-divisor, hence a unit. This is item 1 of the fourth premise, and §4 of the pass-1 review re-derives it.
  - Characters with an intermediate component are charged to `ν_n <= 12η_n`. That covers all of them: their constituents have an intermediate local factor, because root characters kill `J_ρ`.
- **Union bound.** Three events per orbit, each `<= 2q^(-(L+1))`; `{depth_nu >= K}` (origin type) is `U_0`-invariant, so integrating gives `6q^(-(L+1))`.
- **Counting.**
  - `μ_n(E_±) >= μ_n(T ∩ good_±) - η_n^± >= μ_n(T) - 6q^(-(L+1)) - η_n^±`, where `T = {origin, depth_nu >= K}`.
  - `E_+ ∩ E_- = ∅` because `β > 0`. Both lie in `{depth_nu >= K'} ⊇ T`.
  - Adding: `μ_n(T) <= μ_n(K' <= depth_nu < K) + 12q^(-(L+1)) + η_n^+ + η_n^-`.
- **Conclusion.**
  - Item 3 of the fourth premise, `μ_n(d^j < depth_nu <= d^(j+1)) <= η_n` summed over `j < ⌈log_d K⌉`, covers `1 < depth_nu < K`.
  - `β > 0` holds: `λv_d = Σ j v_j > Σ v_j = λv_1` for `A = (min(i,j))`, and `B = PAP^(-1)` has `ℓ_B = P ℓ_A`, `det B = 1`, all entries `>= 1`.
- **Uniformity.** `k` depends only on `d`. `η_n^± = 4δ_n(A^k)^2/κ^2` and `η_n^±(B^k)` tend to 0 for these fixed compressors (item 1 of the first premise). `K` depends only on `L`. So for each fixed `L`, `lim_U` of the right-hand side is `12q^(-(L+1))`, and letting `L -> ∞` gives 0. No rate is used anywhere.
- **Hidden assumptions.** Property (T) enters only through the premises (the Kazhdan constant `κ`). No amenability is used.

## 4. Premises: all ESTABLISHED, all with PASS verdicts

- **`compressor-transport-exactifies-under-vertex-rounding`.**
  - Used: item 3 (total-variation invariance for `A` with all entries `>= 1`) for `A^k` and `B^k`, and item 1.
  - Verdict: PASS, review-backlog §1, including the spectral-measure step.
- **`unit-type-vertex-rounding-forces-compressor-commutant-rigidity`.**
  - Used: item 1 (finite Steinberg images). The claim's title mentions unit type, but item 1 needs only (H1). Swarm2 review §1, Lemma 2.1, confirms this: exponent-`p` root images, an ideal-closed kernel, and `St_r(R_+)/<<x_ij(I)>> ≅ St_r(R_+/I)`.
  - No circularity: unit type is not assumed.
  - Verdict: PASS, swarm2 §1.
- **`vertex-rounding-non-unit-mass-at-origin`.**
  - Used: item 1, intermediate trace `<= 12η_n`.
  - Verdict: PASS, review-backlog §5.
- **`nonunit-component-root-mass-is-log-scale-folner`.**
  - Used: item 1 (componentwise transport) and item 3 (per-scale bound).
  - Verdict: PASS, review-backlog §4, items 2–4.
  - The route's depth, `1 + max{c : c·1 ∈ Sh}`, agrees with the premise's `min{k : χ_nu` trivial on `z^k R_+}` for origin characters.

## 5. Sanity tests and non-blocking notes

- **Toy model: d = 2, q = 2.**
  - Setup: `A_0 = F_2[x,y]/(x^a, y^b)`, `a <= b <= 2a-1`, socle functional `λ_0`, `Sh = [0,a-1] × [0,b-1]`, `M = [[1,1],[1,2]]`.
  - **Atypical u.** For `u = 1`, `e_1(D_M χ_0) = 2a - b - 1`, which can be 0.
  - **Typical u.** Lemma 2(b) says that apart from probability `<= 2^(-L)`, `e_1(D_M χ_0(u·)) >= a - 1 - L`. The independent functionals are the coordinates of `u` at the distinct monomials `x^(a-1-m) y^(b-1-m)`, `m = c..a-1`. This matches the upper bound `a - 1` from Lemma 2(a).
  - **What it shows.** Orbit-typicality is essential, and the route handles it correctly: the one-sided containment fails only on a vanishing fraction of each orbit.
  - **Perron sandwich.** `A^2 e_1 = (2,3)` against `ℓ_1λ^2 v ≈ (1.89, 3.06)`, with ratio `e_1/e_2 -> φ` for `A` and `1/φ` for `B`. Disjoint attractors.
- **Proves-too-much test.** With `η_n = 0` (exact invariance), the argument forces all mass to depth `<= 1`, consistent with a measure invariant under contracting transports. It says nothing about (H1). Against `log-depth-rate-rounding-is-equivalent-to-unit-type`: that claim is an equivalence, and this one proves its item (c) under (H1). No conflict.
- **Notes, none affecting the conclusion.**
  - (i) State the exact identity `h_31(u) x_12(f) h_31(u)^(-1) = x_12(u^(-1) f)` rather than `u^(±1)`.
  - (ii) Say explicitly that `s` is recomputed with `v_B` for `M_-`.
  - (iii) Note `γ_k < 1` in Lemma 3.
  - (iv) The artifact's "nonnegative `M`" in §1 is broader than the first premise, which needs every entry `>= 1`. `A^k` and `B^k` satisfy it.
- **Not assessed:** novelty. Nothing is in Lean.
