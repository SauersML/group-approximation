---
rg: 2
id: lifted-thompson-t-order-type-kernels-riesz-smear-proof
kind: route
title: Invariant kernels on dyadic configurations depend only on order type, translation smearing turns them into a step-function cnd on R, and Riesz automatic continuity removes the steps
target: lifted-thompson-t-order-type-kernels-bounded-on-centre
requires: []
---

**Conventions.**
- `T`, `T̄`, `z`, `r_k`, `X_m`, depth and `H_Y` are as in the target.
- A *cnd kernel* on a set `X` is a symmetric `k : X × X → [0, ∞)` with `k(x,x) = 0` and
  `Σ c_i c_j k(x_i, x_j) <= 0` whenever `Σ c_i = 0`.
- Schoenberg: such a `k` has the form `k(x,y) = ‖β(x) − β(y)‖²` for a map `β` into a real Hilbert
  space, so `√k` is a pseudometric; and `e^{-sk}` is a positive definite kernel for every `s > 0`.
- For `H ≤ G`, cnd functions on `G` that are bi-invariant under `H` correspond exactly to
  `G`-invariant cnd kernels on `G/H`, via `k(gH, hH) = ψ(h^{-1} g)`.

**Step 1: invariant kernels on `X_m` are functions of order type.** For `Y, Y' ∈ X_m`, the
*order type* of `(Y, Y')` is the order relation on the labelled `Z`-periodic set
`{y_i + n} ∪ {y'_j + n}`. That is, it records for all `i, j, n` which of `y_i + n` and `y'_j` is
larger, and whether they are equal. Claim: pairs of the same order type lie in one `T̄`-orbit.

- Let `(Y, Y')` and `(W, W')` have the same order type. Put `A = (Y ∪ Y') + Z` and
  `B = (W ∪ W') + Z`, and let `σ : A → B` be the labelled bijection `y_i + n ↦ w_i + n`,
  `y'_j + n ↦ w'_j + n`. It is well defined, increasing and commutes with `+1`, because the
  order types agree.
- The images `Ā, B̄ ⊂ S^1` are finite sets of dyadic points, and `σ̄` preserves their cyclic
  order. Map each complementary arc of `Ā` onto the corresponding arc of `B̄` by a PL map with
  dyadic breakpoints and slopes in `2^Z`. This is possible because any two dyadic intervals are
  so related (Step 0 of `lifted-thompson-t-convex-line-walls-contraction-proof`). The result is
  some `ḡ ∈ T` with `ḡ = σ̄` on `Ā`.
- Choose the lift `g ∈ T̄` with `g(a_0) = σ(a_0)` for one `a_0 ∈ A`. Both `g|_A` and `σ` are
  increasing bijections `A → B`, where `A` is the full preimage of `Ā`, and they agree at
  `a_0`. Since `A ≅ Z` as an ordered set, they agree on all of `A`. So `g(Y, Y') = (W, W')`.
- The same argument with `Y'` omitted shows that `T̄` acts transitively on `X_m`.

Hence a `T̄`-invariant kernel `k` on `X_m` has the form `k(Y, Y') = κ(type(Y, Y'))`. The same
holds on any `T̄`-invariant subset of `⊔_m X_m`, with types of pairs of different sizes.

**Step 2: the translation smear.** Fix `Y ∈ X_m` of depth `<= d`, and put
`B_Y = (Y − Y) + Z = {y_i − y_j + n}`. Then `B_Y ⊂ 2^{-d}Z` is locally finite, and it contains
`Z`.
- For real `t` the translate `Y + t` is again an increasing `m`-tuple with period data, and it
  lies in `X_m` when `t` is dyadic.
- Translation by a real `s` preserves order types. So `type(Y + s, Y + t) = type(Y, Y + t − s)`.
- `type(Y, Y + t)` changes only when some `y_j + t = y_i + n`, that is, when `t ∈ B_Y`. So it is
  constant on each component of `R \ B_Y`.

Define `Φ(t) = κ(type(Y, Y + t))` for real `t ∉ B_Y`, and `φ(t) = k(Y, Y + t)` for dyadic `t`.
Then:
- (a) `φ = Φ` on dyadic `t ∉ B_Y`, and `Φ` is locally constant on `R \ B_Y`.
- (b) `Φ(−t) = Φ(t)`, by symmetry of `k` and Step 2's translation rule.
- (c) For dyadic `t_1, …, t_N`, `k(Y + t_i, Y + t_j) = φ(t_j − t_i)`.
  So `(t_i, t_j) ↦ φ(t_j − t_i)` is a cnd kernel on the dyadic rationals.

**Step 3: integral positive definiteness.** Fix `s > 0` and put `Ψ = e^{-sΦ}` on `R \ B_Y`,
so `0 < Ψ <= 1`. Claim: `∫∫ f(x) f(y) Ψ(x − y) dx dy >= 0` for every real `f ∈ C_c(R)`.

- Say `supp f ⊂ [−L, L]`. Let `δ = 2^{-M}`, and for each of the finitely many `i` with
  `[iδ, (i+1)δ] ∩ [−L, L] ≠ ∅` choose a dyadic tag `x_i ∈ (iδ, (i+1)δ)` inductively, so that
  `x_i − x_j ∉ B_Y` for all earlier `j`. At each step only finitely many values are excluded,
  because `B_Y` is locally finite, while the interval contains infinitely many dyadics.
- By Step 2(c) and Schoenberg, the matrix `(e^{-s φ(x_i − x_j)})` is positive semidefinite. Its
  diagonal entries are `e^{-s k(Y,Y)} = 1`, and by (a) its off-diagonal entries are
  `Ψ(x_i − x_j)`. So
  `S_δ = δ² Σ_i f(x_i)² + δ² Σ_{i ≠ j} f(x_i) f(x_j) Ψ(x_i − x_j) >= 0`.
- The first term is at most `δ · (2L + 2δ) ‖f‖²_∞`, which tends to `0`.
- `F(x,y) = f(x) f(y) Ψ(x − y)` is bounded on `[−L, L]²`. It is continuous off the finitely many
  lines `x − y = b` with `b ∈ B_Y ∩ [−2L, 2L]`, a Lebesgue-null set. So `F` is Riemann
  integrable.
- The second term is a Riemann sum of `F` over the grid squares of side `δ` minus the diagonal
  squares. Their total area is `O(δ)`, so the second term tends to `∫∫ F`.

Letting `M → ∞` gives the claim. Since `Ψ` is real and even, the cross terms cancel and the
inequality also holds for complex `f`: `∫∫ f(x) \bar f(y) Ψ(x − y) >= 0`.

**Step 4: automatic continuity (F. Riesz 1933; Crum 1956).** A bounded measurable `Ψ` on `R`
that is positive definite in the integral sense of Step 3 agrees a.e. with a continuous positive
definite function. Self-contained sketch:
- Let `ρ_ε` be a mollifier, `ρ̃_ε(x) = ρ_ε(−x)`, and `g_ε = Ψ * ρ_ε * ρ̃_ε`. This is continuous.
- For points `u_i` and complex `c_i`, put `F = Σ c_i ρ_ε(· − u_i)`. Then
  `Σ c_i \bar c_j g_ε(u_i − u_j) = ∫∫ F(x) \bar F(y) Ψ(x − y) dx dy >= 0`. So `g_ε` is positive
  definite in the pointwise sense.
- By Bochner, `g_ε = \hat μ_ε` with `μ_ε >= 0` and `μ_ε(R) = g_ε(0) <= ‖Ψ‖_∞ <= 1`.
- Pass to a vaguely convergent subsequence `μ_ε → μ`, with `μ(R) <= 1`. For Schwartz `h`,
  `∫ g_ε h = ∫ \hat h dμ_ε → ∫ \hat h dμ`, because `\hat h ∈ C_0(R)` and the masses are
  bounded. Also `∫ g_ε h → ∫ Ψ h`, because `g_ε → Ψ` in `L^1_loc`.
- So `Ψ = \hat μ` a.e., and `\hat μ` is continuous.

**Step 5: the steps vanish.** Let `Ψ_c` be the continuous function with `Ψ_c = Ψ` a.e.
- Let `I` be a component of `R \ B_Y`, which is an open interval. On `I`, `Ψ` is a constant
  `e^{-s c_I}`. Since `Ψ_c` is continuous and equals that constant a.e. on `I`, it equals it on
  all of `I`.
- At a point `b ∈ B_Y`, the two adjacent components have the same limit `Ψ_c(b)`, so
  `c_I = c_{I'}`.
- `B_Y` is discrete, so the components are chained by such points. Hence `Φ ≡ c` on `R \ B_Y`.
- In particular `c = φ(2^{-d-1}) = k(Y, r_{d+1} Y)`, since `2^{-d-1} ∉ 2^{-d}Z ⊇ B_Y`.

**Step 6: the break points.** Let `b ∈ B_Y` be dyadic. Choose a dyadic `u ∉ B_Y` with
`b − u ∉ B_Y`; this is possible because `B_Y ∪ (b − B_Y)` is locally finite. By the pseudometric
property and translation invariance,
`√φ(b) = √k(Y, Y + b) <= √k(Y, Y + u) + √k(Y + u, Y + b) = √φ(u) + √φ(b − u) = 2√c`.
So `φ <= 4c` on all dyadics. In particular `k(Y, z^n Y) = φ(n) <= 4 k(Y, r_{d+1} Y)`.

**Conclusions.**
- **(O2).** This is Step 6. The bi-invariant form follows from the dictionary in the
  Conventions, applied to `T̄/H_Y ≅ T̄·Y = X_m` (transitivity, Step 1). A cnd function
  bi-invariant under a group `H' ⊇ H_Y` is in particular `H_Y`-bi-invariant.
- **(O1).** Take `m = 1` and `Y = (0)`, which has depth `0` and `B_Y = Z`. For dyadics
  `x, y`, pick `g ∈ T̄` with `g(0) = x`: lift an element of `T` sending `0` to `x mod 1`, then
  correct by a power of `z`. Then `g^{-1}(y) = t` is dyadic and
  `k(x, y) = k(0, t) = φ(t)`. By Steps 5 and 6, `φ = a := c` off `Z` and `φ <= 4a` on `Z`. So
  `k <= 4a` everywhere, and `ψ(g) = k(g0, 0)` is bounded on `T̄`.
- **(O3).** Apply (O2) termwise: `ψ(z^n) = Σ_i ψ_i(z^n) <= 4 Σ_i ψ_i(r_{d_i+1})`. For fixed `D`,
  `Σ_{d_i <= D} ψ_i(r_{d_i+1}) <= Σ_{d <= D} ψ(r_{d+1}) < ∞`, which gives the depth-escape
  statement.

**Numerical calibration, not part of the proof.**
`experiments/tbar-order-type-kernels-2026-09-17/check.py` (output in `output.txt`) exhibits the
death step at finite density. It also confirms the predicted threshold `N ≈ 1/(0.43 ε)` for a
jump of size `ε`.
