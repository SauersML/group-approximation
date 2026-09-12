# Hyperfinite W*-bundles over countable unions of finite-dimensional compacta are trivial (2026-09-12)

Lane `toms-winter-w-bundles`, a helper for BBSTWW Question 3.14
(`nontrivial-w-star-bundle-with-r-fibres-exists`).  This artifact proves that
the "smallest base shape" recorded on that root cannot carry a witness, and it
sharpens `bauer-gamma-failure-localizes-to-infinite-dim-point`.

## Statement

Let `M` be a strictly separable continuous W*-bundle over a compact metrizable
space `K` with every fibre `π_λ(M) ≅ R`.  For a compact metrizable `X` put
`X_inf` = the points of `X` with no closed neighbourhood of finite covering
dimension, and define the derived sequence

```text
X^(0) = X,   X^(δ+1) = (X^(δ))_inf,   X^(λ) = ∩_{δ<λ} X^(δ)  (λ limit).
```

Let `K^(∞)` be the set where it stabilizes.

**Theorem.**
1. If `K^(δ) = ∅` for some `δ`, then `M ≅ C_σ(K,R)`.  This holds exactly when `K`
   is a countable union of closed finite-dimensional subsets (Remark 2).
2. For every `M`, the non-local-triviality locus satisfies `Z(M) ⊆ K^(∞)`.

Examples of admissible bases include:
- the one-point compactification of a countable disjoint union of cubes `[0,1]^n`;
- a wedge of cubes `[0,1/n]^n` shrinking to a point;
- any compact metrizable countable union of finite-dimensional compacta.

The Hilbert cube does not qualify (Hurewicz: it is not countable-dimensional).

## Tools

- **(O15)** Ozawa, arXiv:1304.3523, Theorem 15 (i) ⟺ (ii), quoted verbatim in
  `r-fibre-w-star-bundle-finite-dim-base-citation`.
- **(O16)** Ozawa, Corollary 16: finite covering dimension implies triviality.
- **(EP)** Restriction to a closed subset `Y` (Evington–Pennig).
  - `M_Y = M/I_Y` is a strictly separable R-fibre bundle over `Y`.
  - The quotient map `q_Y` is onto, and `π_λ = π_λ^Y ∘ q_Y` for `λ ∈ Y`.
  - Recorded in `bauer-gamma-failure-localizes-proof`, step 4.
- **Bounds from traciality.**
  - For contractions `p` and all `z`: `‖pz‖_{2,λ} ≤ ‖z‖_{2,λ}` and `‖zp‖_{2,λ} ≤ ‖z‖_{2,λ}`.
  - Hence `‖[p,z]‖_{2,u} ≤ 2‖z‖_{2,u}`.
  - `‖xy − x'y'‖_2 ≤ ‖x − x'‖_2‖y‖ + ‖x'‖‖y − y'‖_2`.

**Good systems.**  A *δ-good system at λ against a finite set F* is a family
`a = (a_ij)_{i,j=1,2}` in the unit ball of `M` whose defects are all `< δ` in
`‖·‖_{2,λ}`:
- `a_ij* − a_ji`,
- `a_ij a_kl − δ_jk a_il`,
- `a_11 + a_22 − 1`,
- `[a_ij, f]` for `f ∈ F`.

Each defect `z` gives the continuous function `λ ↦ E(z*z)(λ)`.  So the set of
`λ` where `a` is δ-good is **open**.

## Step 1. Lifting from a trivial restriction

**Lemma 1.**  Let `Y ⊆ K` be closed with `M_Y ≅ C_σ(Y,R)`.  For every finite
`F ⊂ M` and `δ > 0` there is a system in `M` that is δ-good at every point of
some open `O ⊇ Y`.

*Proof.*
1. **Matrix approximation.** Let `D_m ⊂ R` be the dyadic matrix subalgebras with
   2-norm dense union. Take `f ∈ F`, viewed in `C_σ(Y,R)`. The functions
   `t ↦ ‖f(t) − E_{D_m}f(t)‖_2` are continuous and decrease to 0 pointwise, so
   uniformly by Dini.
2. **Exact central units.** Choose `m` so that the errors are `< δ/4`. Take exact
   matrix units `e_ij` of `M_2 ⊂ D_m' ∩ R`, as constant sections. They satisfy
   the algebraic relations exactly, and `‖[e_ij, f(t)]‖_2 ≤ 2‖f(t) − E_{D_m} f(t)‖_2 < δ/2`.
3. **Lift.** Lift the `e_ij` through `q_Y` to contractions `a_ij ∈ M`, using
   (EP). All defects are `< δ` at every `λ ∈ Y`, because `π_λ = π_λ^Y ∘ q_Y`.
4. **Neighbourhood.** Openness of the good set gives `O`. ∎

## Step 2. Patching two systems (dimension-free)

**Lemma 2.**  Let `O ⊆ K` be open and let `O', O''` be open with
`cl O' ⊂ O''` and `cl O'' ⊂ O`.  Put `C = K ∖ O'`.  Suppose:
- `a` is δ-good against `F` at every point of `O`;
- `b` is δ-good against `F ∪ {a_ij}` at every point of `C`.

Then there is a system `c ∈ M` that is `Cδ`-good against `F` at every point of
`K`, with `C` an absolute constant.

*Construction.*
1. **Cutoffs.** Urysohn gives `g, κ ∈ C(K, [0,1])`:
   - `g = 0` on `cl O'` and `g = 1` on `K ∖ O''`;
   - `κ = 0` on `cl O''` and `κ = 1` on `K ∖ O`.
2. **Flip and unitary.** Put `w = Σ_{i,j} a_ij b_ji` and `h = (1 − (w + w*)/2)/2`,
   and set
   ```text
   u = exp(iπ g h)          (g is central, so gh is self-adjoint and u is a unitary of M),
   c_ij = (1 − κ)·u a_ij u* + κ·b_ij.
   ```

*Estimates, fibrewise at λ.*  Functional calculus commutes with `π_λ`, so
`π_λ(u) = exp(iπ g(λ) π_λ(h))`.
- **Regime `λ ∈ cl O'`:** `g = κ = 0`, so `π_λ(c) = π_λ(a)`. This is good because `λ ∈ O`.
- **Regime `0 < g(λ) < 1`:** this forces `λ ∈ O'' ∖ cl O' ⊂ O ∩ C`, so both systems are good there.
  - **Flip relations.** Expanding with the relations and `[a_ij, b_kl] ≈ 0`, where every error is `O(δ)`:
    ```text
    w* ≈ w,    w² ≈ (Σ a_ii)(Σ b_jj) ≈ 1,    w a_kl w ≈ (Σ_i a_ii) b_kl ≈ b_kl.
    ```
    So `‖h² − h‖_{2,λ} ≤ Cδ` and `‖[h, f]‖_{2,λ} ≤ Cδ` for `f ∈ F`.
  - **Scalar bound.** On `[−2,2]` the function `t ↦ exp(iπ s t) − 1 − (e^{iπ s} − 1)t` vanishes at `t = 0, 1`. Its quotient by `t(t−1)` is bounded uniformly in `s ∈ [0,1]`. Spectral calculus then gives
    ```text
    ‖u − (1 + (e^{iπs} − 1)h)‖_{2,λ} ≤ C ‖h² − h‖_{2,λ}.
    ```
  - **Consequences.** `‖[u, f]‖_{2,λ} ≤ Cδ`. Since `u` is unitary, `u a u*` has the same relation defects as `a`, and its commutator defects are at most `δ + 2‖[u,f]‖_2`.
  - Here `κ = 0`, so `c = u a u*` is `Cδ`-good.
- **Regime `λ ∈ O ∖ O''`:** `g = 1` and both systems are good, so `π_λ(u) ≈ π_λ(w)` up to `Cδ`, and `u a_ij u* ≈ w a_ij w ≈ b_ij`. The element `c` is a convex combination of two elements within `Cδ` of `b`, hence `Cδ`-good.
- **Regime `λ ∉ O`:** `κ = 1`, so `π_λ(c) = π_λ(b)`, which is good because `λ ∈ C`. The value of `u` there does not matter.

The constant `C` depends only on `k = 2` and on the fixed functional-calculus
bound.  It is independent of `K`, of its dimension, and of the overlap. ∎

## Step 3. Induction on derived length

Call `X` *reducible* if `X^(δ) = ∅` for some `δ`, and let `ℓ(X)` be the least
such `δ`.

**Facts.**
- **(a) `ℓ(X)` is a successor.** At a limit `λ`, the sets `X^(δ)` for `δ < λ`
  would be a decreasing family of nonempty compacta with empty intersection,
  which is impossible.
- **(b) Monotonicity.** For closed `C ⊆ X`, `C^(δ) ⊆ X^(δ) ∩ C`. If `x ∈ A ⊆ B`
  (both closed) and `x` has a finite-dimensional closed neighbourhood `N` in `B`,
  then `N ∩ A` is one in `A`. Induct on `δ`.
- **(c) Finite dimension off `X_inf`.** If `X_inf = ∅`, finitely many interiors of
  finite-dimensional closed neighbourhoods cover `X`. The finite sum theorem gives
  `dim X < ∞`.

**Theorem 1.** If `K` is reducible, `M ≅ C_σ(K,R)`.

*Proof.* Induct on `ℓ(X)` over all reducible `X`, simultaneously for all
bundles over `X`.
- **Cases `ℓ = 0` and `ℓ = 1`.** Here `X = ∅` or `dim X < ∞`, and (O16) applies.
- **Case `ℓ(X) = γ + 1` with `γ ≥ 1`.** Put `Y = X^(γ) ≠ ∅`.
  1. `Y_inf = ∅`, so `dim Y < ∞` by (c). By (O16), `M_Y` is trivial.
  2. **Local good system.** Fix a finite `F ⊂ M` and `δ > 0`. Lemma 1 gives `a`, δ-good on an open `O ⊇ Y`. Choose `O', O''` with `Y ⊂ O'` and `cl O' ⊂ O'' ⊂ cl O'' ⊂ O`.
  3. **Complement.** Put `C = X ∖ O'`, a closed set with `C ∩ Y = ∅`. By (b), `C^(γ) ⊆ X^(γ) ∩ C = ∅`, so `ℓ(C) ≤ γ`. By induction `M_C` is trivial.
  4. **Second system.** Lemma 1, applied to `M` with the closed set `C` and the finite set `F ∪ {a_ij}`, gives `b`, δ-good on a neighbourhood of `C`.
  5. **Patch.** Lemma 2 gives `c`, `Cδ`-good on all of `X`.
  6. **Approximate projection.** Put `x = (c_11 + c_11*)/2 ∈ [−1,1]` and `p = x_+`. Then:
     - `0 ≤ p ≤ 1`;
     - `‖p − x‖_2 ≤ ‖x² − x‖_2 ≤ Cδ`, because `|t_−| ≤ |t² − t|` on `[−1,1]`;
     - `E(p) ≈ 1/2`, from `τ_λ(c_11) ≈ τ_λ(c_12 c_21) = τ_λ(c_21 c_12) ≈ τ_λ(c_22)` and `c_11 + c_22 ≈ 1`;
     - `‖[p, f]‖_{2,u} ≤ Cδ` for `f ∈ F`.
  7. **Sequence.** The strict topology on bounded sets is the ‖·‖_{2,u}-topology. Ozawa uses a strictly dense sequence `(a_n)` in the unit ball of `M` in his proof of Theorem 15. Take `F_n = {a_1, …, a_n}` and `δ_n → 0`. With the commutator bound above, `‖[p_n, a]‖_{2,u} → 0` for every `a` in the unit ball.
  8. So (ii) of (O15) holds, and (O15) gives `M` trivial. ∎

**Remark 2 (which bases are reducible).** For compact metrizable `K`, `K` is
reducible iff `K` is a countable union of closed finite-dimensional subsets.
- *(⇐)* Let `A = ∪ (A ∩ F_n)` be a nonempty closed subset. By Baire, some `A ∩ F_n` has nonempty interior in `A`. So `A_inf ≠ A`, and the derived sequence strictly decreases while nonempty. A strictly decreasing chain of closed sets in a second-countable space is countable, so it reaches `∅`.
- *(⇒)* Each `K^(δ) ∖ K^(δ+1)` is open in `K^(δ)`, hence σ-compact. Each compact piece is covered by finitely many finite-dimensional neighbourhoods, and there are countably many `δ`.

**Corollary 3.** `Z(M) ⊆ K^(∞)` for every `M`.
- Let `z ∉ K^(∞)`, and take a closed neighbourhood `Y` of `z` disjoint from `K^(∞)`.
- By (b), `Y^(δ) ⊆ K^(δ) ∩ Y`, and this is empty at the stabilization index.
- So `Y` is reducible, and `M_Y` is trivial by Theorem 1 applied to `M_Y`.

## Consequences for the graph

- **The smallest base shape is dead.** A witness for
  `nontrivial-w-star-bundle-with-r-fibres-exists` cannot live over the one-point
  compactification of `⊔ [0,1]^n`, nor over any countable-dimensional base. Its
  base must contain a nonempty closed set every nonempty relatively open subset of
  which is infinite-dimensional (for example, a Hilbert cube). The recorded
  requirement that central halving rates degenerate over the n-th cube cannot be
  met: the lift at the added point is uniformly good on a neighbourhood, and
  Lemma 2 patches it to the finite-dimensional remainder at a cost independent of
  dimension.
- **Algebras.** A unital simple separable nuclear non-elementary `A` with `T(A)`
  Bauer and `∂_e T(A)` a countable union of closed finite-dimensional subsets has
  uniform property Gamma (`bauer-uniform-gamma-iff-trivial-tracial-bundle`). With
  `uniform-gamma-algebras-satisfy-toms-winter`, strict comparison then gives
  Z-stability. That overlaps Lin's condition (C)
  (`lin-condition-c-boundary-strict-comparison-z-stable`) on Toms–Winter. Uniform
  Gamma itself needs no comparison hypothesis, and the bundle theorem needs no
  C*-algebra.
- **Where the patching obstruction must live.** Lemma 2 is dimension-free for two
  pieces. Ozawa's dimension enters only when many local systems must be patched
  with compounding errors. Theorem 1 avoids compounding because each induction
  step patches exactly two systems. A witness base therefore needs a kernel
  `K^(∞)` on which no two-piece scheme exists: every neighbourhood of every point
  of `K^(∞)` is infinite-dimensional within `K^(∞)` itself.

## Trust surfaces and novelty

- (O15) and (O16) are quoted from the PDF. (EP) is as recorded in the localization proof. Nothing is in Lean.
- **Novelty check, bounded.** Ozawa's Corollary 12 already patches clopen pieces in dimension 0, and flip homotopies are standard (Dadarlat–Winter, Hirshberg–Rørdam–Winter). I found no statement of Theorem 1 for countable-dimensional bases; the search was limited.
- **Consistency.** The known infinite-dimensional failures for C(X)-algebras with strongly self-absorbing fibres (Hirshberg–Rørdam–Winter) use product-of-spheres bases, which are not countable-dimensional. They do not contradict Theorem 1.
