---
rg: 2
id: fp-v-times-subshift-full-group-connected-differences-proof
kind: route
title: Lift the full group to a linear action on the V-orbit times the Λ-orbit with a two-dimensional fibre that switches basis on one half of a split difference set, then glue and recur
target: fp-v-times-subshift-full-groups-force-connected-differences
requires: [v-times-ample-full-groups-are-generated-by-transpositions]
---

The notation is that of the target. The import is used only for the Corollary (`F(T) = A(T)`).
Parts 1–3 use only:
- Tietze: a finitely presented group is finitely presented on every finite generating set;
- the product topology of `T = G_V × (Λ ⋉ X)`.

Fix a field `k`.

## 0. Normal forms

**Lemma N.** Every `g ∈ F(T)` has *normal-form data*: finitely many tuples
`(u_i, v_i, F_i, π_i, λ_i)` with the following properties.
- `u_i, v_i` are finite binary words, `F_i ⊆ Λ` is finite, `π_i ∈ A^(F_i)`, and `λ_i ∈ Λ`.
- The rectangles `[u_i] × [π_i]` partition `C × X`, where `[π] = {x' ∈ X : x'|_(F_i) = π}`.
- On `[u_i] × [π_i]`, `g(u_i w, x') = (v_i w, λ_i.x')`.

*Proof.* `g` is given by a compact open bisection `B` of `T` whose source and range are all of
`C × X`. A basis of the topology of `T` consists of products
`{[f, c] : c ∈ U} × ({λ} × W)`, with `f ∈ V`, `U ⊆ C` open and `W ⊆ X` open. By compactness,
finitely many such basic sets, each contained in `B`, cover `B`.
- Every `f ∈ V` acts as a prefix replacement on every sufficiently small cylinder.
- The cylinders `[π]` form a basis of `X`.

So the source `C × X` has a finite cover by rectangles `[u] × [π]`, each inside the source of a
basic set on which `B` acts by `(uw, x') -> (vw, λ.x')`. Refine to a partition: take all words
`u` of one large length and all patterns on one large ball. `∎`

Prefix replacements preserve the set `C_0` of eventually-zero sequences. Choose normal-form data
for each element of a finite generating set once and for all.

## 1. Coarse connectivity (part 1)

**Generators and relators.** Let `Γ ≤ F(T)` be finitely presented, containing every `t_s` and
`e_a`.
- By Tietze, `Γ` has a presentation on a finite set `Σ` that is closed under inverses and
  contains every `t_s` and `e_a`. It is a monoid presentation by words `w` with relations
  `w = 1`, including `σσ^(-1) = 1`. Let every relator have length `<= n`.
- Choose normal-form data for each `σ ∈ Σ`.
  - For `t_s`: one tuple `(∅, ∅, ∅, ∅, s)`.
  - For `e_a`: the tuples `(00, 01, {1}, a, 1)`, `(01, 1, {1}, a, 1)` and `(1, 00, {1}, a, 1)`,
    and `(∅, ∅, {1}, b, 1)` for `b ≠ a`.
- Let `r` bound the radii of all `F_i` (so `F_i ⊆ B_r`), and `ℓ` bound all `|λ_i|`.
- Put `R = nℓ + r` and `m = 2R`.

**The orbit action.** Fix `x ∈ X`. Since `Λ` acts freely,
`β_x : C_0 × Λ -> C × X`, `(c, z) -> (c, z.x)`, is injective. Its image is `Γ`-invariant by Lemma N,
so `Γ` acts on `C_0 × Λ`. For `σ ∈ Σ`, the point `(c, z)` goes to `(v_i w, λ_i z)`, where `i` is the
unique index with `c = u_i w` and `z.x ∈ [π_i]`, that is, `x(z^(-1) f) = π_i(f)` for all `f ∈ F_i`.

**The representation.** Fix `x, y ∈ X`, and suppose `Δ(x, y) = Δ_1 ⊔ Δ_2` with both parts nonempty
and `d(Δ_1, Δ_2) > m`. Put `T_0 = [[1, 1], [0, 1]] ∈ GL_2(k)`. For `q ∈ Λ` and `a ∈ A` put
`D_a(q) = diag([x(q) = a], [y(q) = a])`, and
- `M_a(q) = D_a(q)` if `q ∉ Δ_2`;
- `M_a(q) = T_0 D_a(q) T_0^(-1)` if `q ∈ Δ_2`.

If `q ∉ Δ`, then `D_a(q)` is scalar, so both formulas agree there. For a pattern `π ∈ A^F` and
`z ∈ Λ`, put `M_π(z) = ∏_(f ∈ F) M_(π(f))(z^(-1) f)` in a fixed order of `F` (empty product `I`).

Let `W` have basis `δ_c ⊗ δ_z ⊗ v` (`c ∈ C_0`, `z ∈ Λ`, `v` in the standard basis of `k^2`).
For `σ ∈ Σ` with data `(u_i, v_i, F_i, π_i, λ_i)`, define `ψ(σ) ∈ End(W)`:

    ψ(σ)(δ_c ⊗ δ_z ⊗ v) = Σ_(i : c ∈ [u_i]) δ_(v_i w_i) ⊗ δ_(λ_i z) ⊗ M_(π_i)(z) v,

where `c = u_i w_i` in the `i`-th term. Extend `ψ` to words in `Σ`, multiplying right to left.

**Locality.** Let `w = σ_j ··· σ_1` with `j <= n`, and apply `ψ(w)` to `δ_c ⊗ δ_z ⊗ v`.
- After `k` letters every term sits at a site `μz` with `|μ| <= kℓ`.
- The next letter uses matrices `M_a(q)` with `q ∈ (μz)^(-1) F_i ⊆ z^(-1) B_(kℓ + r)`.

So every matrix used is some `M_a(q)` with `q ∈ Z := z^(-1) B_R`. The set `Z` has diameter `<= 2R = m`,
since `d(z^(-1) p, z^(-1) p') = |p^(-1) p'|`. So `Z` does not meet both `Δ_1` and `Δ_2`.

**Relators act trivially.** Let `w` be a relator, so `w = 1` in `Γ`.
- **If `Z` misses `Δ_2`,** every matrix used is `D_a(q)`. Then `M_(π_i)(z') e_1 = [z'.x ∈ [π_i]] e_1`
  for each site `z'` reached. For fixed `c'`, the sets `[π_i]` with `c' ∈ [u_i]` partition `X`, so
  exactly one term survives. By induction on the letters,
  `ψ(w)(δ_c ⊗ δ_z ⊗ e_1) = δ_(c') ⊗ δ_(z') ⊗ e_1`, where `(c', z') = w.(c, z)` for the orbit action
  of `x`. That point is `(c, z)`. The same holds for `e_2` with the orbit action of `y`.
- **If `Z` misses `Δ_1`,** every matrix used equals `T_0 D_a(q) T_0^(-1)`: on `Δ_2` by definition,
  and off `Δ` because `D_a(q)` is scalar. Every product of such matrices is `T_0 (∏ D) T_0^(-1)`.
  So `ψ(w)(δ_c ⊗ δ_z ⊗ T_0 v) = (1 ⊗ 1 ⊗ T_0)` applied to the computation of the previous case,
  which is `δ_c ⊗ δ_z ⊗ T_0 v`.

Hence `ψ(w) = I` for every relator. In particular every `ψ(σ)` is invertible, and `ψ` defines a
homomorphism `Γ -> GL(W)`.

**Two special elements.**
- `ψ(t_s)(δ_c ⊗ δ_z ⊗ v) = δ_c ⊗ δ_(sz) ⊗ v`. So for any `g ∈ Λ`, writing `t_g` for the
  translation by `g` (a word in the `t_s`), `ψ(t_g)` sends `δ_z` to `δ_(gz)` with trivial fibre.
- `Σ_(b ∈ A) M_b(q) = I` in both cases. So, with `H` the permutation operator `δ_c -> δ_(hc)` on
  `k[C_0]` and `P_z = M_a(z^(-1))`,

      ψ(e_a)(δ_c ⊗ δ_z ⊗ v) = δ_(hc) ⊗ δ_z ⊗ P_z v + δ_c ⊗ δ_z ⊗ (I - P_z) v.

**A commutator that `ψ` does not respect.** Pick `p ∈ Δ_1` and `q ∈ Δ_2`, with `a = x(p)` and
`b = x(q)`. Put `g_1 = t_(p^(-1))^(-1) e_a t_(p^(-1))` and `g_2 = t_(q^(-1))^(-1) e_b t_(q^(-1))`, both in `Γ`.
- **In `Γ`.** `t_(p^(-1))` sends `x'` to `p^(-1).x'`, and `(p^(-1).x')(1) = x'(p)`. So `g_1` applies `h` to
  `c` when `x'(p) = a`, and is the identity otherwise. Likewise `g_2` applies `h` when `x'(q) = b`.
  Both have the form `(c, x') -> (h^(ε(x')) c, x')`, so they commute. As `Γ ≤ F(T)`, `[g_1, g_2] = 1` in `Γ`.
- **In `ψ`, at the site `z = 1`.** `ψ(t_(p^(-1)))` moves `δ_1` to `δ_(p^(-1))`, where `ψ(e_a)` uses
  `M_a(p)`, and `ψ(t_(p^(-1)))^(-1)` moves back. On the invariant subspace `k[C_0] ⊗ δ_1 ⊗ k^2`:

      ψ(g_1) = I + (H - 1) ⊗ P,  P = M_a(p) = diag(1, 0)  (since y(p) ≠ x(p) = a),
      ψ(g_2) = I + (H - 1) ⊗ Q,  Q = M_b(q) = T_0 diag(1, 0) T_0^(-1) = [[1, -1], [0, 0]].

  So `ψ(g_1) ψ(g_2) - ψ(g_2) ψ(g_1) = (H - 1)^2 ⊗ (PQ - QP)`, and `PQ - QP = [[0, -1], [0, 0]]`.
  For `c = 0^∞`, the points `c`, `hc = 010^∞` and `h^2 c = 10^∞` are distinct. So `(H - 1)^2 δ_c` has
  coefficient `1` at `δ_c`, and the difference sends `δ_c ⊗ δ_1 ⊗ e_2` to a nonzero vector.

This contradicts `ψ` being a homomorphism of `Γ`. So no such split exists, and every `Δ(x, y)` is
`m`-connected, with `m = 2(nℓ + r)` depending only on the chosen presentation and data. `∎`

## 2. Gluing lemma

**Lemma G.** Let `X` be defined by allowed patterns on the windows `pB_(r_X)`. Let `x ∈ X`. Let
`Δ_1, ..., Δ_t ⊆ Λ` be pairwise at distance `> 2r_X`, and write `N(Δ_i)` for the set of points
within distance `2r_X` of `Δ_i`. Let `y_i ∈ X` with `y_i = x` on `N(Δ_i) \ Δ_i`. Then the
configuration `z` with `z = y_i` on `Δ_i` and `z = x` elsewhere lies in `X`.

*Proof.* A window `pB_(r_X)` has diameter `<= 2r_X`.
- **If it meets `Δ_i`,** it lies in `N(Δ_i)` and meets no other `Δ_j`. On it `z = y_i`: on `Δ_i` by
  definition, and elsewhere because `z = x = y_i` there.
- **If it meets no `Δ_i`,** then `z = x` on it.

Either way `z` reads an allowed pattern. `∎`

## 3. No finite asymptotic pairs (part 2)

Let `X` be minimal and of finite type with window radius `r_X`, and let `m` be as in Section 1.

**Uniform recurrence.** Let `π ∈ L_F(X)` for a finite `F`, with open nonempty cylinder `[π]`.
- By minimality the translates `g[π]` cover `X`: the complement of their union is closed,
  invariant and not all of `X`.
- By compactness finitely many `g_1[π], ..., g_t[π]` cover `X`.
- For `x ∈ X` and `c ∈ Λ`, some `i` has `g_i^(-1) c^(-1).x ∈ [π]`, that is, `x(c g_i f) = π(f)` for
  `f ∈ F`.

So `x` carries `π` within distance `L = max |g_i|` of every point. Since `Λ` is infinite, the
occurrences are unbounded.

**The argument.** Suppose `x ≠ y` in `X` with `Δ = Δ(x, y) ⊆ B_M` finite and nonempty. Put
`F = B_(M + 2r_X)` and `π = x|_F`.
- Recurrence gives `g` with `x(gf) = x(f)` for all `f ∈ F` and `|g| > 2M + m + 2r_X`. Then
  `d(Δ, gΔ) >= |g| - 2M > max(m, 2r_X)`.
- Apply Lemma G to `x` with `Δ_1 = Δ`, `y_1 = y`, and `Δ_2 = gΔ`, `y_2 = g.y`.
  - `N(Δ) ⊆ F`, and `y = x` on `F \ Δ`.
  - `N(gΔ) = gN(Δ)`. For `f ∈ N(Δ) \ Δ`, `(g.y)(gf) = y(f) = x(f) = x(gf)`.
- The resulting `z ∈ X` has `Δ(x, z) = Δ ⊔ gΔ`: on `gΔ`, `z(gf) = y(f) ≠ x(f) = x(gf)`.
- These two nonempty parts are at distance `> m`, which contradicts part 1. `∎`

## 4. Boundary layers (part 3)

**Injectivity.** Keep the hypotheses of Section 3 and write `r = r_X`. Let `F` be finite,
`∂F = {p ∈ F : pB_(2r) ⊄ F}` and `I = F \ ∂F`. Suppose `π_1 ≠ π_2` in `L_F(X)` agree on `∂F`.
- Pick `x ∈ X` with `x|_F = π_1`, and define `z = π_2` on `F` and `z = x` off `F`.
- A window `pB_r` meeting `I` at `q` lies in `qB_(2r) ⊆ F`. There it reads a subpattern of
  `π_2 ∈ L_F(X)`, which is allowed.
- A window missing `I` reads `x`, since `π_1 = π_2` on `∂F`.
- So `z ∈ X`, and `Δ(x, z) ⊆ I` is finite and nonempty, which contradicts part 2.

Hence restriction `L_F(X) -> L_(∂F)(X)` is injective, and `|L_F(X)| <= |A|^|∂F|`.

**Amenable `Λ`.** Let `(F_j)` be right Følner: `|F_j b \ F_j| / |F_j| -> 0` for each `b`.
- If `p ∈ ∂F_j`, some `b ∈ B_(2r)` has `pb ∈ F_j b \ F_j`. Hence
  `|∂F_j| <= Σ_(b ∈ B_(2r)) |F_j b \ F_j| = o(|F_j|)`, and `log |L_(F_j)(X)| = o(|F_j|)`.
- Topological entropy is the limit of `log |L_(F_j)(X)| / |F_j|` along right Følner sequences
  (Ornstein–Weiss; recalled, not re-read; for `Z^d` it is the usual definition). So `h_top(X) = 0`.

**`Z^d`.** `∂B_N ⊆ B_N \ B_(N - 2r)`, which has `O(N^(d-1))` points.

**Infinite virtually cyclic `Λ`.** Choose an infinite cyclic normal subgroup `<t>` of finite index
and a finite transversal `K_0`, so `Λ = <t> K_0`. Put `F_N = {t^j c : |j| <= N, c ∈ K_0}`.
- Write `cb = t^i c'` for `c ∈ K_0`, `b ∈ B_(2r)` and `c' ∈ K_0`. There is a uniform `K` with `|i| <= K`.
- Then `t^j cb = t^(j+i) c'`, so `∂F_N ⊆ {t^j c : N - K < |j| <= N}`, which has at most `2K|K_0|` points.
- Every finite set lies in some `F_N`, so `|L_(K')(X)| <= |A|^(2K|K_0|)` for every finite `K'`.
  Finitely many distinct points are separated by one finite window, so `X` is finite. `∎`

## 5. Remarks

- **Corollary.** `F(T) = A(T)` by `v-times-ample-full-groups-are-generated-by-transpositions`, and
  `F(T)` contains every `t_s` and `e_a` (the latter is a 3-cycle of a degree-3 multisection). If
  `A(T)` is finitely presented, take `Γ = F(T)`.
- **Part 1 needs neither finite type nor minimality,** only freeness, which makes `β_x` injective.
- **Sketch, not used: over amenable `Λ`, a minimal SFT has a finite asymptotic pair iff it has
  positive entropy.** If `π_1 ≠ π_2` in `L_F(X)` agree on `∂F`, Section 4 builds a finite
  asymptotic pair. Conversely, from a pair `x, y` with `Δ ⊆ B_M`, uniform recurrence gives
  occurrences of `x|_(B_(M + 2r))` in `x` within distance `L` of every point. A maximal
  `D`-separated set of them, with `D > 2M + 4r`, is `(D + L)`-dense. Lemma G flips any subset
  independently, so a right Følner set `F_j` carries `2^(c|F_j|)` patterns for some `c > 0`. So the
  hypothesis "no finite asymptotic pairs" of P2's hosts is exactly zero entropy there, and the
  obstruction bites only on positive-entropy minimal SFTs, whose existence is not settled here.
- **The basis switch is the crossed-product one.** The algebra analogue for Cantor crossed
  products (fp-crossed-products-force-connected-differences on main) switches basis the same way.
  The group version adds the `C_0` factor so that site-conditioned 3-cycles `e_a` replace the
  idempotents `χ[x(1) = a]`, and uses `(H - 1)^2 ≠ 0` for the commutator.
