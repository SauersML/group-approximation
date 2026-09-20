---
rg: 2
id: thompson-t-cup-classes-split-along-dilation-eigenlines-proof
kind: route
title: Direct sums and scalings make the cup-product classes a subspace; averaging over the finite centre of the half-rotation centralizer descends cup products, so the transfer J preserves them; translation numbers double and Godbillon-Vey sums halve under descent, giving eigenvalues 1/2 and 2
target: thompson-t-cup-classes-split-along-dilation-eigenlines
requires: []
artifacts:
  - experiments/kahler-dilation-2026-09-17/check_gv_dilation.py
---

Notation is that of the target. Cochains are real, inhomogeneous, with
`(δc)(f, g, h) = c(g, h) − c(fg, h) + c(f, gh) − c(f, g)` and `(δφ)(g, h) = φ(g) + φ(h) − φ(gh)`.
The torus cycle of commuting `g, h` is `[g | h] − [h | g]`. Its boundary is
`[g] + [h] − [gh] − [h] − [g] + [hg] = 0`, so `⟨c, σ⟩ = c(g, h) − c(h, g)` for a cocycle `c`, and
this vanishes when `c` is a coboundary.

**Imported (literature, cited as stated in `thompson-t-co-amenable-bounded-euler-powers-proof`).**
- **[GS]** Ghys–Sergiescu, Comment. Math. Helv. 62 (1987): "`H^*(T; Q) ≅ Q[α, χ]/(αχ)`, where `χ`
  is the Euler class". Used only in Step 6, for `dim H²(T; R) = 2` and `e_R ≠ 0`.
- **[FFLM, Mo]** `H^*_b(T; R) ≅ R[e_b]` (arXiv:2111.04305, arXiv:2112.13741), used only for the
  last bullet of part (4).
- **[HS]** Hochschild–Serre: for a central extension `1 → A → C → T → 1` with `A` finite,
  inflation `H^n(T; R) → H^n(C; R)` is an isomorphism, because `H^q(A; R) = 0` for `q > 0`
  (Brown, *Cohomology of Groups*, VII.6). This is textbook.

## Step 1. Cup products are well defined on classes; K is a subspace

*Cocycle.* Let `c = b_1 ∪ b_2`. Expand `c(fg, h)` and `c(f, gh)` with the cocycle identities.
- `c(fg, h) = ⟨b_1(f), π(fg)b_2(h)⟩ + ⟨π(f)b_1(g), π(fg)b_2(h)⟩`. By orthogonality the second
  term is `c(g, h)`.
- `c(f, gh) = ⟨b_1(f), π(f)b_2(g)⟩ + ⟨b_1(f), π(fg)b_2(h)⟩ = c(f, g) + ⟨b_1(f), π(fg)b_2(h)⟩`.
- Hence `δc = c(g,h) − c(g,h) − ⟨b_1(f), π(fg)b_2(h)⟩ + c(f,g) + ⟨b_1(f), π(fg)b_2(h)⟩ − c(f,g) = 0`.

*Class depends only on `[b_1], [b_2]`.*
- If `b_1` is replaced by `b_1 + (π(·)v − v)`, then `c` changes by
  `⟨π(g)v − v, π(g)b_2(h)⟩ = ⟨v, b_2(h) − π(g)b_2(h)⟩ = ⟨v, b_2(g) + b_2(h) − b_2(gh)⟩ = δφ`,
  with `φ = ⟨v, b_2(·)⟩`.
- If `b_2` is replaced by `b_2 + (π(·)w − w)`, then `c` changes by
  `⟨b_1(g), π(gh)w⟩ − ⟨b_1(g), π(g)w⟩`. With `ψ(g) = ⟨b_1(g), π(g)w⟩`, expanding `ψ(gh)` by the
  cocycle identity gives `δψ(g, h) = ⟨b_1(g), π(g)w⟩ − ⟨b_1(g), π(gh)w⟩`. So the change is `−δψ`.

*Subspace.*
- `(π, s b_1, b_2)` realizes `s[c]` for every `s ∈ R`. In particular `0 ∈ K` and `−[c] ∈ K`.
- `(π ⊕ π', b_1 ⊕ b_1', b_2 ⊕ b_2')` realizes `[c] + [c']`.

*Pullback.* For a homomorphism `φ : G → T`, `(π∘φ, b_1∘φ, b_2∘φ)` realizes `φ^*[c]`. Write
`K_G` for the cup-product classes of `G`. Then `φ^* K_T ⊂ K_G`. For `G = T` this is the
endomorphism clause of part (1).

## Step 2. The half-rotation centralizer and descent

Let `g ∈ C`, and let `ĝ : R → R` be a lift of `g`.
- *Lifts commute with `x ↦ x + 1/2`.* Both `ĝ(x + 1/2)` and `ĝ(x) + 1/2` lift `gr = rg`, so they
  differ by an integer `m`, constant by continuity. Applying this twice gives
  `ĝ(x + 1) = ĝ(x) + 1 + 2m`. Since `ĝ(x + 1) = ĝ(x) + 1`, we get `m = 0`.
- *Descent.* Put `Φ(ĝ)(u) = 2 ĝ(u/2)`. It commutes with `u ↦ u + 1`, and it is dyadic PL:
  conjugation by `x ↦ 2x` preserves dyadic breakpoints and power-of-2 slopes.
  - So `p(g) = Φ(ĝ) mod 1` lies in `T`.
  - Changing the lift `ĝ` by an integer `n` changes `Φ(ĝ)` by `2n`, so `p` is well defined.
  - `Φ(ĝ ĥ) = Φ(ĝ) Φ(ĥ)`, so `p` is a homomorphism.
- *Onto.* For `f ∈ T` with lift `F`, the map `x ↦ F(2x)/2` commutes with `x ↦ x + 1/2`. It is a
  dyadic PL lift of an element `g ∈ C` with `p(g) = f`.
- *Kernel.* `p(g) = 1` means `2ĝ(u/2) = u + n`, that is `ĝ(x) = x + n/2`. So `ker p = {1, r} = A`,
  which is central in `C` because `C` centralizes `r`.
- *Local data.*
  - `g(y + 1/2) = g(y) + 1/2` gives `v_g(y + 1/2) = v_g(y)`.
  - `p(g)(2y) = 2g(y)`, and the dilation preserves orientation and the one-sided sides, so
    `v_{p(g)}(2y) = v_g(y)` for all `y`.

## Step 3. Cup products descend through the finite centre: K_C = p^* K_T

- `p^* K_T ⊂ K_C` by Step 1 (pullback).
- *Normalize on `A`.* Let `(π, b_1, b_2)` be data for `C` on `H`. The restriction `b_i|_A` is a
  cocycle of a finite group. With `u_i = −(1/2) Σ_{a ∈ A} b_i(a)`, the cocycle identity gives
  `π(a)u_i − u_i = −(1/2) Σ_{a'} (b_i(aa') − b_i(a')) + b_i(a) = b_i(a)`.
  So `b_i' = b_i − (π(·)u_i − u_i)` is cohomologous to `b_i` and vanishes on `A`.
- *Values lie in `H^A`.* For `a ∈ A` and `g ∈ C`:
  - `b_i'(ga) = b_i'(g) + π(g)b_i'(a) = b_i'(g)`;
  - `b_i'(ag) = b_i'(a) + π(a)b_i'(g) = π(a)b_i'(g)`;
  - `ag = ga`, so `π(a)b_i'(g) = b_i'(g)`.
- *Descend.* `H^A` is `π(C)`-invariant, since `A` is central, and `A` acts trivially on it. So
  `π̄(p(g)) = π(g)|_{H^A}` and `b̄_i(p(g)) = b_i'(g)` are well defined, by right `A`-invariance
  of `b_i'`. They form an orthogonal representation of `T` with two cocycles.
- `b_1' ∪ b_2'` only involves values in `H^A`, so it equals `p^*(b̄_1 ∪ b̄_2)`. By Step 1,
  `[b_1 ∪ b_2] = [b_1' ∪ b_2'] = p^*[b̄_1 ∪ b̄_2]`, and so `K_C ⊂ p^* K_T`.
- By [HS], `p^*` is an isomorphism on `H²(−; R)`. So `J = (p^*)^{-1} i^*` is defined, and
  `J(K_T) = (p^*)^{-1}(i^* K_T) ⊂ (p^*)^{-1}(K_C) = K_T`. This proves part (1).
- *Explicit form of `J` on witnesses.* `J[b_1 ∪ b_2] = [b̄_1 ∪ b̄_2]`, where `(π̄, b̄_i)` is
  built from `(π|_C, b_i|_C)` as above.

## Step 4. J(e_R) = e_R / 2

- Let `T̄` be the group of lifts, `z(x) = x + 1`, and `τ` the translation number
  `τ(x) = lim x^n(0)/n` on `T̄`.
  - `τ` is conjugation invariant.
  - `τ(z^m x) = m + τ(x)`.
  - `τ(Φ(x)) = 2τ(x)`, because `Φ(x)^n(0) = 2 x^n(0)`.
- Fix a section `s : T → T̄` and write `s(g)s(h) = z^{ε(g,h)} s(gh)`. Then `ε` is the integral
  Euler cocycle, and `e_R = [ε]`.
- Put `D(g, h) = τ(ĝ ĥ) − τ(ĝ) − τ(ĥ)` for lifts `ĝ, ĥ`. It is independent of the lifts, by the
  shift rule. With `ĝ = s(g)` and `ĥ = s(h)`, it equals `ε(g, h) − δ(τ∘s)(g, h)`. So `[D] = e_R`.
- For `g, h ∈ C`:
  - `i^* e_R = [D(g, h)]`.
  - `p^* e_R = [D(p g, p h)]`. Computed with the lifts `Φ(ĝ), Φ(ĥ)`, this is
    `τ(Φ(ĝĥ)) − τ(Φ ĝ) − τ(Φ ĥ) = 2 D(g, h)`.
  - So `p^* e_R = 2 i^* e_R`, and `J(e_R) = e_R/2`.
- *Tori.* Let `gh = hg` in `T`, with lifts `ĝ, ĥ`.
  - Their commutator is a lift of `1`, so `ĝ ĥ ĝ^{-1} = z^n ĥ`.
  - Applying `τ` gives `τ(ĥ) = n + τ(ĥ)`, so `n = 0`, and the lifts commute.
  - The pulled-back extension of `Z²` is then abelian, hence split, so `⟨e_R, τ⟩ = 0` for
    every torus class `τ`.

## Step 5. The discrete Godbillon-Vey cocycle: J(gv) = 2 gv, ⟨gv, σ_t⟩ = 2, J_* σ_t = 2 σ_t

*Finiteness and chain rule.*
- If `g` has no breakpoint at `y` and `f` has none at `gy`, then both vectors are diagonal and
  `det(v_g(y), v_f(gy)) = 0`. So `Ω(f, g)` is a finite sum.
- One-sided chain rule: `v_{fg}(y) = v_f(gy) + v_g(y)`.

*Cocycle.* Reindex `Ω(f, g)` by `x = hy`, a bijection of `S^1`. Then all four terms of `δΩ` are
finitely supported functions of `y`:
- `Ω(g, h)` gives `det(v_h(y), v_g(hy))`;
- `−Ω(fg, h)` gives `−det(v_h(y), v_f(ghy) + v_g(hy))`;
- `Ω(f, gh)` gives `det(v_g(hy) + v_h(y), v_f(ghy))`;
- `−Ω(f, g)` gives `−det(v_g(hy), v_f(ghy))`.

By bilinearity they cancel pointwise, so `δΩ = 0`.

*`J(gv) = 2 gv`.* Let `g, h ∈ C`. By Step 2 (local data), `Ω(p g, p h)` equals
`Σ_{u ∈ S^1} det(v_{ph}(u), v_{pg}(ph·u))`. Substitute `u = 2y` with `y ∈ [0, 1/2)`:
- `v_{ph}(2y) = v_h(y)`;
- `ph(2y) = 2h(y)`, so `v_{pg}(ph·u) = v_{pg}(2h(y)) = v_g(hy)`.

So `Ω(pg, ph) = Σ_{y ∈ [0,1/2)} det(v_h(y), v_g(hy))`. The summand of `i^*Ω(g, h)` is
`1/2`-periodic in `y`, because `v_h(y + 1/2) = v_h(y)` and `h(y + 1/2) = h(y) + 1/2`. Hence
`i^*Ω = 2 p^*Ω` as cocycles on `C`, and `J(gv) = 2 gv`.

*Torus values.* Let `g, h` commute, with supports `[a, c]` and `[c, b]` (`b ≠ a`) meeting only at
`c`.
- A term of `Ω(g, h)` is nonzero only if `y ∈ supp h` and `hy ∈ supp g ∩ supp h = {c}`. Since `h`
  fixes `c`, this forces `y = c`.
- At `c`: `v_g(c) = (ℓ, 0)` and `v_h(c) = (0, ρ)`, with `ℓ = log_2 g'_-(c)` and
  `ρ = log_2 h'_+(c)`.
- So `Ω(g, h) = det((0, ρ), (ℓ, 0)) = −ℓρ`. Symmetrically, `Ω(h, g) = det((ℓ, 0), (0, ρ)) = ℓρ`.
- The torus value is `−2ℓρ`.
- If the supports meet at several such points, the contributions add. Each point where `g` is on
  the left contributes `−2ℓρ`.

For `(g_0, h_0)` of the target: `c = 1/2`, `ℓ = −1` (last piece of `g_0` has slope 1/2), and
`ρ = 1` (first piece of `h_0` has slope 2). So `⟨gv, σ_t⟩ = 2`. In particular `σ_t ≠ 0` in
`H_2(T; R)` and `gv ≠ 0`.

*`J_* σ_t = 2 σ_t`.* `J_* = i_* (p_*)^{-1}` on `H_2(T; R)` is the transpose of `J`.
- Let `g_1 ∈ C` act on each half circle `[j/2, (j+1)/2)` by `x ↦ j/2 + g_0(2x − j)/2`. Define
  `h_1` likewise.
- Then `p(g_1) = g_0` and `p(h_1) = h_0`, and `g_1, h_1` commute: their supports are
  `[1/8, 1/4] ∪ [5/8, 3/4]` and `[1/4, 3/8] ∪ [3/4, 7/8]`.
- So `(p_*)^{-1} σ_t` is the torus class of `(g_1, h_1)` in `C`, and `J_* σ_t` is that torus in
  `T`.
- Its supports meet at `1/4` and `3/4`, with `g_1` on the left at both. Slopes are preserved by
  the dilation, so `ℓ = −1` and `ρ = 1` at both. Hence `⟨gv, J_* σ_t⟩ = 4`.
- Also `⟨e_R, J_* σ_t⟩ = 0` (it is a torus).

Under [GS] (Step 6), `ann(e_R) ⊂ H_2(T; R)` is a line containing `σ_t`, so `J_* σ_t = 2σ_t`. The
computation is checked by exact rational arithmetic in
`experiments/kahler-dilation-2026-09-17/check_gv_dilation.py`. The script covers the cocycle
identity on random triples, `⟨gv, σ_t⟩ = 2`, `⟨gv, J_*σ_t⟩ = 4`, and `i^*Ω = 2 p^*Ω` on random
pairs in `C`.

## Step 6. Projection and dichotomy

*Part (3).* Let `c = λ e_R + μ gv ∈ K`. Then:
- `J(c) = λ e_R/2 + 2μ gv ∈ K` by Step 3;
- `2c − J(c) = (3/2) λ e_R ∈ K` by Step 1.

The witness is the direct sum stated in the target, with `(π̄, b̄_i)` from Step 3. This part uses
no import.

*Part (4).*
- By [GS], `H²(T; Q)` in degree 2 is spanned by `α` and `χ`, so `dim H²(T; R) = 2` and `e_R ≠ 0`.
- `e_R` and `gv` are eigenvectors of `J` with eigenvalues `1/2 ≠ 2`, and both are nonzero (Steps
  4, 5). So they form a basis, and `J = diag(1/2, 2)`.
- A `J`-invariant subspace of `R²` for a diagonal map with distinct eigenvalues is `0`, one of the
  two eigenlines, or everything. By part (1), `K` is one of these.
- So `e_R ∈ K` iff `K ⊄ R gv`. That is, (K) holds iff some cup product is not a multiple of `gv`;
  if so, part (3) produces an explicit witness.
- *Torus form.* For `c = λ e_R + μ gv`, `⟨c, σ_t⟩ = 2μ` by Steps 4 and 5. So a non-exact cup
  product with `⟨c, σ_t⟩ = 0` is `λ e_R` with `λ ≠ 0`. Conversely, `e_R` itself has
  `⟨e_R, σ_t⟩ = 0`.
- *Boundedness.* If `gv` were bounded, it would lie in the image of `H²_b(T; R) = R e_b`, which is
  `R e_R` [FFLM, Mo]. That contradicts linear independence.

## Checks on scope

- No step uses anything about `π` beyond orthogonality. So the dichotomy covers every witness
  class. It does not decide (K).
- The two non-trivial alternatives that remain are `K = R gv` (all cup products are
  Godbillon–Vey) and `K = 0` (all cup products exact). Both are falsifiable. Exhibiting one cup
  product off the `gv` line proves (K). Exhibiting a nonzero cup product on the `gv` line, plus an
  obstruction to the `σ_e` pairing, refutes it.

## Step 7. Growth test for the gv component (part (5))

- *Iterated half-lifts.* Iterating the half-lift of Step 5 `n` times on `(g_0, h_0)` gives the
  pair `(g_n, h_n)` of the target.
  - The Step 5 argument applies verbatim to any commuting pair `(g, h)` and its half-lifts: `J_*`
    sends the torus of `(g, h)` to the torus of the half-lifts. So `J_*^n σ_t` is the torus of
    `(g_n, h_n)`.
  - Under [GS], `J_* σ_t = 2σ_t` (Step 5), so `J_*^n σ_t = 2^n σ_t`.
- *Evaluate.* Let `c = b_1 ∪ b_2` with `[c] = λ e_R + μ gv`. Then:
  - `2^{n+1} μ = ⟨[c], 2^n σ_t⟩ = c(g_n, h_n) − c(h_n, g_n)`;
  - `|c(g, h)| = |⟨b_1(g), π(g)b_2(h)⟩| ≤ ‖b_1(g)‖ ‖b_2(h)‖`.

  Together these give the stated bound.
- *Consequence.* If the liminf vanishes and `c` is non-exact, then `μ = 0` and `λ ≠ 0`. So
  `e_R = λ^{-1}[c] ∈ K`.
- *Jump cocycle.* Put `j_g(y) = log_2 g'_+(y) − log_2 g'_-(y)`.
  - The one-sided chain rule gives `j_{gh}(y) = j_g(hy) + j_h(y)`, so
    `b(g) = Σ_y j_g(y) δ_{gy}` is a cocycle into the permutation representation `ℓ²(Z[1/2]/Z)`.
  - `g_0` is the identity near `0`, so `g_n` has exactly `2^n` scaled copies of the breakpoints
    of `g_0`, with the same jumps. Hence `‖b(g_n)‖² = 2^n ‖b(g_0)‖²`.
  - This is the borderline rate in the bound, so part (5) does not exclude `gv` for local
    `ℓ²`-additive cocycles. It does exclude it for every pair with `o(2^{n/2})` growth on the
    towers.
