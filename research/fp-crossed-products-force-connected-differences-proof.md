---
rg: 2
id: fp-crossed-products-force-connected-differences-proof
kind: route
title: A two-dimensional sitewise representation that switches basis on one half of a split difference set, then gluing and recurrence
target: fp-crossed-products-force-connected-differences
requires: [fp-crossed-products-force-sft-over-any-group]
---

The notation is that of the target. The proof is complete here and uses only elementary facts:
- finite presentation of an algebra does not depend on the finite generating set (Tietze);
- the algebraic crossed product is a free left `LC(X, k)`-module on `{u_g}`;
- the monomial formula of `fp-crossed-products-force-sft-over-any-group-proof`, step 2.

## 1. Coarse connectivity (part 1)

**Monomials in `B_X`.** Let `W` be a word in the letters `E_a, U_s`, of length `<= n`.
- Let `g_W ∈ P` be the product of its `U`-letters.
- Let `p_1, ..., p_m` be, for its successive `E`-letters `E_(a_1), ..., E_(a_m)`, the products of
  the `U`-letters to the left of each. So `|p_i| <= n`.

Since `u_p e_a u_p^(-1) = χ[x(p) = a]`, the image of `W` in `B_X` is `c_W u_(g_W)` with
`c_W(x) = ∏_i [x(p_i) = a_i]` (the step-2 formula). A relator `ρ = Σ_W λ_W W` therefore vanishes in
`B_X` iff, for every `g ∈ P` and every `x ∈ X`,

    (★)  Σ_(g_W = g) λ_W ∏_i [x(p_i) = a_i] = 0,

using that `B_X = ⊕_g LC(X, k) u_g`.

**The representation.** Fix `x, y ∈ X`, and suppose `Δ = Δ(x, y) = Δ_1 ⊔ Δ_2` with both parts nonempty
and `d(Δ_1, Δ_2) > 2n`. Put `T = [[1, 1], [0, 1]] ∈ GL_2(k)`. For `q ∈ P` and `a ∈ A`, define
`M_a(q) ∈ M_2(k)`:
- `M_a(q) = diag([x(q) = a], [y(q) = a])` if `q ∉ Δ_2`;
- `M_a(q) = T diag([x(q) = a], [y(q) = a]) T^(-1)` if `q ∈ Δ_2`.

If `q ∉ Δ`, the diagonal matrix is scalar and commutes with `T`, so both formulas agree there.

Let `V` have basis `δ_z ⊗ v` (`z ∈ P`, `v ∈ k^2`). Define a representation `ψ` of the free
algebra `k<E_a, U_s>` on `V`:
- `ψ(U_s)(δ_z ⊗ v) = δ_(sz) ⊗ v`;
- `ψ(E_a)(δ_z ⊗ v) = δ_z ⊗ M_a(z^(-1)) v`.

**Monomials in `ψ`.** Apply `ψ(W)` to `δ_z ⊗ v`, reading right to left.
- Just before the `i`-th `E`-letter is applied, the site is `p_i^(-1) g_W z`.
- So that letter applies `M_(a_i)(z^(-1) g_W^(-1) p_i)`.
- With `w = g_W z`:

    ψ(W)(δ_z ⊗ v) = δ_w ⊗ M_(a_1)(w^(-1) p_1) ··· M_(a_m)(w^(-1) p_m) v.

**Relators act by zero.** Fix a relator `ρ`, a site `z` and `g ∈ P`, and put `w = gz`. The
`δ_w`-component of `ψ(ρ)(δ_z ⊗ v)` is `Σ_(g_W = g) λ_W ∏_i M_(a_i)(w^(-1) p_i) v`.
- All sites `w^(-1) p_i` lie in `w^(-1) B_n`. This set has diameter `<= 2n`, since
  `d(w^(-1) p, w^(-1) q) = |p^(-1) q|`. So it does not meet both `Δ_1` and `Δ_2`.
- **If it misses `Δ_2`,** every factor is diagonal. The sum is the diagonal matrix with entries
  `Σ λ_W ∏ [x(w^(-1) p_i) = a_i]` and `Σ λ_W ∏ [y(w^(-1) p_i) = a_i]`. Since
  `x(w^(-1) p) = (w.x)(p)`, these are (★) at `w.x ∈ X` and at `w.y ∈ X`, so both vanish.
- **If it misses `Δ_1`,** every factor has the form `T (diagonal) T^(-1)`: on `Δ_2` by definition,
  and off `Δ` because the factor is scalar. So the sum is `T diag(...) T^(-1)` with the same two
  vanishing entries.

Hence `ψ(ρ) = 0`.

**A kernel element that `ψ` does not kill.** Pick `p ∈ Δ_1` and `q ∈ Δ_2`, with `a = x(p)` and
`b = x(q)`. Choose words `U_p`, `U_q` in the `U_s` representing `p` and `q`, with formal inverses
`U_(p^(-1))`, `U_(q^(-1))`. Put

    Θ = U_p E_a U_(p^(-1)) U_q E_b U_(q^(-1)) - U_q E_b U_(q^(-1)) U_p E_a U_(p^(-1)).

- **In `B_X`.** `Θ` maps to `[χ[x(p) = a], χ[x(q) = b]] = 0`, since both are functions.
- **In `ψ`, at the site `z = 1`.** `U_p E_a U_(p^(-1))` acts by `M_a(p)`, and
  `M_a(p) = diag(1, 0)` because `y(p) ≠ x(p) = a`. `U_q E_b U_(q^(-1))` acts by
  `M_b(q) = T diag(1, 0) T^(-1) = [[1, -1], [0, 0]]`. Their commutator is `[[0, -1], [0, 0]] ≠ 0`,
  over every field.

If the relators generated the kernel of `k<E_a, U_s> -> B_X`, then `ψ` would kill `Θ`. So no
presentation with relators of length `<= n` exists, and every `Δ(x, y)` is `2n`-connected. `∎`

## 2. Gluing lemma

**Lemma G.** Let `X` be defined by allowed patterns on the windows `p B_r`. Let `x ∈ X`. Let
`Δ_1, ..., Δ_t ⊆ P` be pairwise at distance `> 2r`, and write `N(Δ_i)` for the set of points
within distance `2r` of `Δ_i`. Let `y_i ∈ X` with `y_i = x` on `N(Δ_i) \ Δ_i`. Then the
configuration `z` with `z = y_i` on `Δ_i` and `z = x` elsewhere lies in `X`.

*Proof.* A window `p B_r` has diameter `<= 2r`.
- **If it meets `Δ_i`,** it lies in `N(Δ_i)` and meets no other `Δ_j`. On it, `z = y_i`: on `Δ_i`
  by definition, and elsewhere because `z = x = y_i` there.
- **If it meets no `Δ_i`,** then `z = x` on it.

Either way `z` reads an allowed pattern. `∎`

This is used in two forms:
- `Δ_i` is the far part of a component of the complement of a ball
  (`fp-minimal-crossed-products-map-onto-ends-proof`, Section 2);
- `Δ_i` is a translate of a finite difference set (Section 3 below).

## 3. No finite asymptotic pairs (part 2)

Let `P` be infinite, `X` minimal, and `B_X` finitely presented. By Tietze, it has a presentation on
`e_a, u_s` with relators of length `<= n` for some `n`. By
`fp-crossed-products-force-sft-over-any-group`, `X` is an SFT with some window radius `r`.

**Uniform recurrence.** Let `π ∈ L_F(X)` for a finite `F`, and `[π] = {x' ∈ X : x'|_F = π}`, which is
open and nonempty.
- By minimality the translates `g[π]` cover `X`, since the complement of their union is closed,
  invariant and not all of `X`.
- By compactness, finitely many `g_1[π], ..., g_t[π]` cover `X`.
- For `x ∈ X` and `c ∈ P`, some `i` has `g_i^(-1) c^(-1).x ∈ [π]`, that is, `x(c g_i h) = π(h)` for
  `h ∈ F`.

So `x` carries `π` within distance `L = max |g_i|` of every point. Since `P` is infinite, the
occurrences are unbounded.

**The argument.** Suppose `x ≠ y` in `X` with `Δ = Δ(x, y) ⊆ B_m` finite and nonempty. Put
`F = B_(m + 2r)` and `π = x|_F`.
- Recurrence gives `g` with `x(gh) = x(h)` for all `h ∈ F` and `|g| > 2m + 2n + 4r`. Then
  `d(Δ, gΔ) >= |g| - 2m > max(2n, 2r)`.
- Apply Lemma G to `x` with `Δ_1 = Δ`, `y_1 = y`, and `Δ_2 = gΔ`, `y_2 = g.y`.
  - `N(Δ) ⊆ F`, and `y = x` on `F \ Δ`.
  - `N(gΔ) = gN(Δ)`. For `h ∈ N(Δ) \ Δ`, `(g.y)(gh) = y(h) = x(h) = x(gh)`.
- The resulting `z ∈ X` has `Δ(x, z) = Δ ⊔ gΔ`. On `gΔ`, `z(gh) = y(h) ≠ x(h) = x(gh)`.
- These two nonempty parts are at distance `> 2n`, which contradicts part 1. `∎`

## 4. Boundary layers (part 3)

**Injectivity.** Keep the hypotheses of Section 3. Let `F` be finite,
`∂F = {p ∈ F : p B_(2r) ⊄ F}` and `I = F \ ∂F`. Suppose `π_1 ≠ π_2` in `L_F(X)` agree on `∂F`.
- Pick `x ∈ X` with `x|_F = π_1`, and define `z = π_2` on `F` and `z = x` off `F`.
- A window `p B_r` meeting `I` at `q` lies in `q B_(2r) ⊆ F`. There it reads a subpattern of
  `π_2 ∈ L_F(X)`, which is allowed.
- A window missing `I` reads `x`, since `π_1 = π_2` on `∂F`.
- So `z ∈ X`, and `Δ(x, z) ⊆ I` is finite and nonempty, which contradicts part 2.

Hence restriction `L_F(X) -> L_(∂F)(X)` is injective, and `|L_F(X)| <= |A|^|∂F|`.

**Amenable `P`.** Let `(F_j)` be right Følner: `|F_j b \ F_j| / |F_j| -> 0` for each `b`.
- If `p ∈ ∂F_j`, some `b ∈ B_(2r)` has `pb ∈ F_j b \ F_j`. Hence
  `|∂F_j| <= Σ_(b ∈ B_(2r)) |F_j b \ F_j| = o(|F_j|)`, and `log |L_(F_j)(X)| = o(|F_j|)`.
- For windows `gF`, topological entropy is the limit of `log |L_(F_j)(X)| / |F_j|` along right
  Følner sequences. This is recalled (Ornstein–Weiss, not re-read); for `Z^d` it is the usual
  definition. So `h_top(X) = 0`.

**`Z^d`.** `∂B_N ⊆ B_N \ B_(N - 2r)`, which has `O(N^(d-1))` points.

**Infinite virtually cyclic `P`.** Choose an infinite cyclic normal subgroup `<t>` of finite index and
a finite transversal `C`, so that `P = <t> C`. Put `F_N = {t^j c : |j| <= N, c ∈ C}`.
- Write `cb = t^i c'` for `c ∈ C`, `b ∈ B_(2r)` and `c' ∈ C`. There is a uniform `K` with `|i| <= K`.
- Then `t^j c b = t^(j+i) c'`. So `∂F_N ⊆ {t^j c : N - K < |j| <= N}`, which has at most `2K|C|`
  points.
- Every finite `K' ⊆ P` lies in some `F_N`, so `|L_(K')(X)| <= |A|^(2K|C|)`. Finitely many distinct
  points are separated by one finite window, so `X` has at most `|A|^(2K|C|)` points.
- This contradicts minimality of an infinite `X`. `∎`

## 5. Remarks

- Part 1 needs neither finite type nor minimality.
- The width `2n` is explicit. Over `Z^2` it is the wall certificate of
  `sft-crossed-product-fp-iff-quantum-rigid` (route step 1), with the same `W = k^2`.
