---
rg: 2
id: regular-germ-extension-attractors-are-undistorted-proof
kind: route
title: Singularity count and depth-gain Lipschitz length functions grow linearly along wandering singularities and attractors
target: regular-germ-extension-attractors-are-undistorted
requires: []
---

Notation as in the claim. A **germ** at `x` is an equivalence class of maps
defined near `x`. A **`V`-germ** is the germ of an element of `V`; `V`-germs are
closed under composition and inversion. So if `β_1, β_2` are `V`-germs and `γ` is
not, then `β_2 γ β_1` is not a `V`-germ.

**Step 0. The depth-gain cocycle.** If `x ∉ sing(h)` and `h(x) ∉ sing(g)`, then
`δ_x(gh) = δ_x(h) + δ_(h(x))(g)`, and `δ_(g(x))(g^-1) = -δ_x(g)`. Near a point
`x ∉ sing(h)`, `h` is one prefix replacement, so `δ(h)` is constant near `x`.

A prefix replacement `c z -> d z` multiplies `μ` by `2^(-(|d|-|c|))`. For clopen
`K`, the open set `K \ sing(h)` is a countable disjoint union of cones on each of
which `h` is a single prefix replacement (take the maximal such cones), and
finite sets are `μ`-null. Hence
`μ(h(K)) = ∫_K 2^(-δ_x(h)) dμ(x) >= 2^(-Lip(h)) μ(K)`.

**Step 1. `s` is a length function.** If `h` is non-singular at `x` and `g` is
non-singular at `h(x)`, then `gh` agrees near `x` with a product of two elements of
`V`. So `sing(gh) ⊆ sing(h) ∪ h^-1(sing(g))`. Also `sing(g^-1) = g(sing(g))`.

**Step 2. Germs at a singular point of a regular `G`.** Let `p ∈ sing(G)`. By (E),
`p = u w^∞` with `w` primitive.
- *`(V)_p = <τ_p> ≅ Z`,* where `τ_p` is the germ of `u y -> u w y`. This is Step 2
  of `orbit-preserving-germ-corollary-rationality-proof`: a `V`-germ fixing `p` is
  `c y -> d y` with `c, d` prefixes of `p`, and primitivity gives `d = u w^k s`
  when `c = u s`.
- *Some `σ_p = τ_p^N` is central in `(G)_p`.* If `(V)_p` is normal, put `N = 1`. If
  it has finite index, its normal core is `<τ_p^N>` for some `N >= 1`. Either way
  each `h ∈ (G)_p` sends `τ_p^N` to `τ_p^(±N)`. A conjugate of a contracting germ is
  contracting, and `τ_p^(-N)` is expanding, so the sign is `+`. This is Step 3 of
  the same route.

**Levels.** Write `σ = σ_p`, represented by `u y -> u w^N y` on `U = cone(u)`, and
put `c = N|w|`. Then `D = U \ σ(U)` is clopen and nonempty, `U \ {p}` is the
disjoint union of the `σ^m(D)`, `m >= 0`, and `ℓ(x) = m` on `σ^m(D)`. Moreover
`δ(σ^j) = jc` on `U`, and `μ(σ^m(U)) = 2^(-mc) μ(U)`.

**Lemma A.** Let `h ∈ Homeo(C)` fix `p`, with germ commuting with `σ`. There is
`L_h` such that on `{ℓ >= L_h}`:
- `h σ = σ h`;
- `h` is non-singular;
- `ℓ(h x) - ℓ(x)` and `δ_x(h)` are bounded and depend only on the class of `x`
  modulo `σ`.

*Proof.* `hσ = σh` holds on some neighbourhood of `p`, hence on `{ℓ >= L_0}`. Take
`L_h >= L_0` so large that the finitely many singular points of `h` other than `p`
lie outside `{ℓ >= L_h}`, and that `h(K) ⊆ U \ {p}` for `K = σ^(L_h)(D)`.

Every `x` with `ℓ(x) >= L_h` is `σ^j(x_0)` with `x_0 ∈ K`, and `h(x) = σ^j h(x_0)` by
induction on `j`. So `ℓ(hx) - ℓ(x) = ℓ(h x_0) - L_h`. For `δ`, compare the cocycle
identities for `h σ^j` and `σ^j h`. The two `σ^j` terms both equal `jc`, so
`δ_(σ^j x_0)(h) = δ_(x_0)(h)`.

On the compact set `K`, the map `h` is non-singular, so `δ(h)` is locally constant
there and takes finitely many values. The compact set `h(K)` meets finitely many
levels. ∎

**Step 3. `Lip` is a length function on a regular `G`.** Fix `g`, with singular
points `y_1, ..., y_r`.
- By (T), `g(y_i) = v_i(y_i)` with `v_i ∈ V`. Then `h_i = v_i^-1 g` fixes `y_i`, and
  its germ lies in `(G)_(y_i)`, so it commutes with `σ_(y_i)` (Step 2).
- By Lemma A, `δ(h_i)` is bounded on a punctured neighbourhood `N_i` of `y_i`. So is
  `δ(g) = δ(h_i) + δ(v_i) ∘ h_i`, since `v_i ∈ V` has finitely many `δ`-values.
- On the compact set `C \ ∪ N_i`, `g` is non-singular and `δ(g)` is locally constant.

So `Lip(g) < ∞`. Subadditivity holds at the cofinitely many points where Step 0
applies. At the remaining non-singular points of `gh` it holds by local constancy
of `δ(gh)`. Finally `Lip(g^-1) = Lip(g)` by Step 0.

**Step 4. Wandering singularities (statement 3).** Let `s_m = a^m(s_0)` with all
`s_m` distinct. Let `s_i, s_j` be the first and last points of `O ∩ sing(a)`, and
`γ` the germ of `a^(j-i+1)` at `s_i`, assumed not a `V`-germ.

Take `n > j - i` and `j - n + 1 <= m <= i`. The germ of `a^n` at `s_m` is the
composite of three germs:
- the germ of `a^(i-m)` at `s_m`, which passes only non-singular points of `a` and
  so is a `V`-germ;
- then `γ`;
- then the germ of `a^(m+n-1-j)` at `s_(j+1)`, again a `V`-germ.

By the groupoid remark this composite is not a `V`-germ, so `s_m ∈ sing(a^n)`.
There are `n - (j - i)` such `m`, giving distinct points.

**Step 5. Attractors (statement 4).** Let `y` be a periodic point of `a`, of period
`q`, and attracting. So there is a clopen `U_0 ∋ y` with `a^q(U_0) ⊆ U_0` and
`∩_n a^(qn)(U_0) = {y}`. A repelling point of `a` is an attracting point of `a^-1`,
and `Lip(a^-n) = Lip(a^n)`.

The decreasing compacta `a^(qn)(U_0)` shrink to `y`. So for every neighbourhood `Y`
of `y`, `a^(qn)(U_0) ⊆ Y` for all large `n`. (★)

*(i) `y ∉ sing(a^q)`.* The germ of `a^q` at `y` is a nontrivial `V`-germ fixing `y`.
- By Step 1 of `orbit-preserving-germ-corollary-rationality-proof`, a `V`-germ fixing
  a point that is not eventually periodic is trivial. So `y = u w^∞`.
- By Step 2 above, the germ is `τ_y^e`, and `e > 0` because `τ_y^e` is expanding for
  `e < 0`.
- On a cone `Z = cone(u w^(j_0))` where `a^q = τ_y^e`, which is `τ_y`-invariant, we
  get `a^(qn) = τ_y^(en)`.

So `Lip(a^(qn)) >= en|w|`.

*(ii) `y ∈ sing(a^q) ⊆ sing(G)`.* Use the levels of Step 2 at `p = y`. The germ of
`a^q` commutes with `σ`. Let `L_A = L_(a^q)` be given by Lemma A.
- **Setting up `W`.** By (★) choose `n_1` with `W = a^(q n_1)(U_0) ⊆ σ^(L_A)(U)`.
  Then `W` is forward-invariant under `a^q`. Choose `L >= L_A` with
  `σ^L(U) ⊆ W`, and put `K = σ^L(D)`.
- **The key inequality.** Lemma A applies along every `a^q`-orbit starting in
  `W \ {y}`. By (★) choose `n_0` with `a^(q n_0)(W) ⊆ σ^(L+1)(U)`. Then
  `ℓ(a^(q n_0) x) >= ℓ(x) + 1` for `x ∈ K`.
- **Spreading it over `σ^L(U)`.** Equivariance on `{ℓ >= L_A}` makes
  `ℓ(a^(q n_0) x) - ℓ(x)` constant along `σ`-classes. So the inequality holds on
  `σ^L(U) \ {y}`, and that set is mapped into itself. By induction
  `ℓ(a^(q n_0 m) x) >= ℓ(x) + m` there.

Hence `a^(q n_0 m)(K) ⊆ σ^(L+m)(U)`, while `μ(K) = 2^(-Lc) μ(D)`. By Step 0,
`Lip(a^(q n_0 m)) >= mc - log_2(μ(U)/μ(D))`.

*Conclusion.* In both cases there are `Q >= 1`, `c' > 0` and `C_0` with
`Lip(a^(Qm)) >= c'm - C_0`. For `n = Qm + r` with `0 <= r < Q`, Step 3 gives
`Lip(a^n) >= Lip(a^(Qm)) - Q Lip(a)`. So `Lip(a^n)` grows linearly.

**Step 6. Consequences (statement 5).** Let `λ` be `s` (Step 4) or `Lip` (Step 5),
with `λ(a^n) >= cn - C`.
- **Undistorted.** If `S` is a finite generating set of `H ∋ a`, then
  `λ(g) <= |g|_S max_S λ`. So `|a^n|_S >= (cn - C)/max_S λ`.
- **No proper-power conjugacy.** Suppose `t a t^-1 = a^k`. If `k <= -2`, replace
  `t, k` by `t^2, k^2`, so assume `k >= 2`. Then `a^(k^j) = t^j a t^-j`. Hence
  `c k^j - C <= λ(a^(k^j)) <= λ(a) + 2j λ(t)`, which fails for large `j`.
- **No Heisenberg centre.** If `a = [x, y]` is central in `<x, y> ≅ H_3(Z)`, then
  `a^(n^2) = [x^n, y^n]`. Hence `c n^2 - C <= 2n (λ(x) + λ(y))`, which fails for
  large `n`.

The Corollary's conjugacies are direct matrix computations:
- `diag(2,1) t_q diag(2,1)^-1 = t_(2q)` in `Aff(Q) <= GL_2(Q)`, where `t_q` is
  translation by `q`;
- `diag(2,1/2) u(q) diag(2,1/2)^-1 = u(4q)` for `u(q) = [[1,q],[0,1]]`;
- `[e_12(1), e_23(q)] = e_13(q)`, which is central in the Heisenberg group the two
  elements generate.

Statement 3 and Step 6 give the first bullet of the Corollary for any finite germ
extension; statement 4 and Step 6 give the second for regular `G`. ∎
