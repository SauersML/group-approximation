---
rg: 2
id: fg-central-simple-cuntz-swindle-algebras-exist-proof
kind: route
title: Coordinate formulas make germ equality generic on boxes with distinct large finite values, which kills singular functions and the off-unit centre; the insertion map h gives the swindle
target: fg-central-simple-cuntz-swindle-algebras-exist
requires:
  - cepss-nonhausdorff-steinberg-simplicity
---

Notation is that of the target. Maps compose right to left. A **box** is a set
`{x ∈ X : x_j ∈ C_j for j ∈ Q}`, where `Q ⊂ Z` is finite and each `C_j` is `{n}` or `[n, ∞]`
with `n ∈ N`. Boxes are clopen and form a basis of `X`; the empty set counts as a box.

## 0. Basic facts

- `X` is compact, metrizable, zero-dimensional and has no isolated points, so it is a Cantor space.
- `h` is a homeomorphism; its inverse deletes coordinate 0.
- The ranges of `s_1` and `s_2` are the complementary clopen sets `{x_0 = 0}` and `{x_0 ≥ 1}`.
  Hence in `A`: `s_i* s_i = 1_X = 1`, `s_1* s_2 = s_2* s_1 = 0`, and `s_1 s_1* + s_2 s_2* = 1`.
  Here `s_i* = 1_([s_i^(-1)])`.
- `Σ` consists of the finite composites of the 7 partial maps `s_1^(±1), s_2^(±1), S^(±1), τ`.
  This set is closed under inverses, since `(ab)^(-1) = b^(-1) a^(-1)`.
- `𝒢` has the basic compact open bisections `[φ, U] = {[φ, x] : x ∈ U}`, for `φ ∈ Σ` and `U`
  clopen in `dom φ`.
- `𝒢` is ample, and second countable because `Σ` is countable. Its unit space `X` is Hausdorff.
- `A_K(𝒢)` is spanned by the `1_([φ,U])`, and `f(γ) = Σ_(i : γ ∈ [φ_i, U_i]) a_i` for
  `f = Σ a_i 1_([φ_i, U_i])`.
- `𝒢` is effective, as every germ groupoid is. Suppose `[φ, x]` has an open bisection
  neighbourhood `[φ, U]` made of isotropy. Then `φ = id` on `U`, so `[φ, x] = [id, x]`.
- `𝒢` is not Hausdorff. Take `z` with `z_0 = z_1 = ∞`. Then `τ = id` on the open sets
  `{x_0 = x_1 = n}`, which accumulate at `z`, but `[τ, z] ≠ [id, z]`.

## 1. Formal-form lemma

Call a partial map `φ` of `X` **formal** if its domain `D` is a box and there are integers
`a ≤ b` and `d_-, d_+` with the following properties. For `x ∈ D`:
- `φ(x)_i = x_(i+d_-)` for `i < a`;
- `φ(x)_i = x_(i+d_+)` for `i > b`;
- for each `a ≤ i ≤ b`, either `φ(x)_i = k_i`, a constant in `N`, or `φ(x)_i = x_(π(i)) + c_i`,
  with `π(i) ∈ Z` and `c_i ∈ Z`, using `∞ + c = ∞`.

Call these the **window formulas** of `φ`. A formal map can always be given a larger window,
because a coordinate outside the window has the formula `x_(i+d) + 0`.

**Lemma 1.** Every `φ ∈ Σ` is formal.

*Proof.* The generators are formal:
- `s_1`: `d_- = 0`, `d_+ = -1`, window `{0}` with constant 0.
- `s_1^(-1)`: domain `{x_0 = 0}`, `d_- = 0`, `d_+ = +1`, empty window. Take `a = 0`, `b = -1`, or
  equivalently window `{0}` with formula `x_1 + 0`.
- `s_2^(±1)`: domain `X` or `{x_0 ≥ 1}`, `d_± = 0`, window `{0}` with `x_0 ± 1`.
- `S^(±1)`: `d_± = ±1`, empty window.
- `τ`: `d_± = 0`, window `{0, 1}` with `x_1, x_0`.

Formal maps are closed under composition. Let `φ, ψ` be formal.
- **Domain.** `dom(φψ) = D_ψ ∩ ψ^(-1)(D_φ)`. Let `{y_i ∈ C}` be one constraint of `D_φ`.
  Its preimage in `D_ψ` is:
  - `D_ψ` or `∅` if `ψ(x)_i` is a constant;
  - `{x_(π(i)) ∈ (C − c) ∩ αN}` if `ψ(x)_i = x_(π(i)) + c`. Here `({n} − c) ∩ αN` is `{n − c}` or
    `∅`, and `([n, ∞] − c) ∩ αN = [max(n − c, 0), ∞]`.

  So it is a box constraint or trivial. Intersections of single-coordinate constraints of these two
  shapes are again of these shapes or empty. So `dom(φψ)` is a box.
- **Formulas.** Substitute `ψ`'s formulas into `φ`'s. A constant stays a constant, and
  `x_j + c` composed with `x_(j') + c'` gives `x_(j') + (c + c')`. For `|i|` large,
  `(φψ(x))_i = x_(i + d^φ + d^ψ)` on the appropriate side. So `φψ` is formal, with a larger
  window. ∎

## 2. Generic-stability lemma

**Lemma 2.** Let `z ∈ X`, let `Φ ⊂ Σ` be finite with `z ∈ dom φ` for all `φ ∈ Φ`, and let `O` be
a neighbourhood of `z`. Then there is a nonempty clopen `V ⊆ O` such that, for all `φ, ψ ∈ Φ`:
- (E) if `[φ, z] = [ψ, z]`, then `φ = ψ` on `V`;
- (D) if `[φ, z] ≠ [ψ, z]`, then `[φ, x] ≠ [ψ, x]` for every `x ∈ V`.

In particular the partition of `Φ` by germ equality at `x` is the same for every `x ∈ V` as at `z`.

*Proof.*

**Step 1: shrink O.** For each pair with `[φ, z] = [ψ, z]`, pick a neighbourhood of `z` on which
`φ = ψ`, and intersect these with `O` and with every `dom φ`, `φ ∈ Φ`. The result contains a box
`B_0 ∋ z`. Each constraint of `B_0` on a coordinate `j` contains `z_j`. Shrinking `B_0`, we may
assume the constraint is `{z_j}` when `z_j < ∞` and `[n_j, ∞]` when `z_j = ∞`.

**Step 2: the data J, C, M.**
- Give all `φ ∈ Φ` a common window `[a, b]`.
- Let `J` be the finite set of coordinates that are either constrained by `B_0` or equal to some
  `π(i)` in a window formula of some `φ ∈ Φ`.
- Let `C` be the largest `|k_i|`, `|c_i|` appearing, and let `n^*` be the largest `n_j` from `B_0`.
- Let `M > n^* + 2C + max{z_j : j ∈ J, z_j < ∞}`.
- List `J_∞ = {j ∈ J : z_j = ∞}` as `j_1, ..., j_m`, and put `v_r = M + r(2C + 1)`.

Let `V` be the box that fixes `x_j = z_j` for `j ∈ J \ J_∞` and `x_(j_r) = v_r`. Then
`∅ ≠ V ⊆ B_0 ⊆ O`, and every point of `V` has the same finite value `u_j` at each `j ∈ J`.
Part (E) holds because `V ⊆ B_0`.

**Step 3: an auxiliary box N.** Let `N` be the box that fixes `x_j = z_j` for `j ∈ J \ J_∞` and
requires `x_j ≥ M` for `j ∈ J_∞`. Then `z ∈ N ⊆ B_0` and `V ⊆ N`.

**Step 4: part (D).** Let `[φ, z] ≠ [ψ, z]`. It suffices to show that `Eq = {x : φ(x) = ψ(x)}`
contains no nonempty box `B ⊆ V`. Indeed, `V` is open, so every neighbourhood of any `x ∈ V`
contains such a box around `x`. Then `φ ≠ ψ` somewhere in every neighbourhood of `x`, so
`[φ, x] ≠ [ψ, x]`.

Suppose, for contradiction, that `∅ ≠ B ⊆ V ∩ Eq` is a box. We show that `φ = ψ` on all of `N`.
Since `N` is a neighbourhood of `z`, this gives `[φ, z] = [ψ, z]`, which is a contradiction.
- **Tails.** Suppose `d_+^φ ≠ d_+^ψ`. Pick `i > b` such that `i + d_+^φ` and `i + d_+^ψ` are both
  outside the finitely many coordinates constrained by `B`. Then some `y ∈ B` has
  `y_(i+d_+^φ) ≠ y_(i+d_+^ψ)`, so `φ(y)_i ≠ ψ(y)_i`, which is impossible. So `d_+^φ = d_+^ψ`, and
  likewise `d_-^φ = d_-^ψ`. Hence the two maps have the same formula on every coordinate outside
  `[a, b]`.
- **Window.** Fix `i ∈ [a, b]`, with formula `F` for `φ` and `G` for `ψ`. Every coordinate they
  mention lies in `J`, and on `B` it takes the fixed finite value `u_j`. So `F = G` on `B` reduces
  to one numerical identity. The possible cases are:
  1. `F` and `G` are the same formula, including equal constants. Then `F = G` everywhere.
  2. `F` and `G` are different constants. This is impossible.
  3. `F = k` and `G = x_j + c`, so `k = u_j + c`.
     - If `z_j < ∞`, then `N` fixes `x_j = z_j = u_j`, so `F = G` on `N`.
     - If `z_j = ∞`, then `u_j ≥ M > 2C ≥ k − c`, which is impossible.
  4. `F = x_j + c` and `G = x_j + c'` with `c ≠ c'`. This is impossible, since `u_j < ∞`.
  5. `F = x_j + c` and `G = x_(j') + c'` with `j ≠ j'`, so `u_j + c = u_(j') + c'`.
     - Both `z_j, z_(j') < ∞`: `N` fixes both, so `F = G` on `N`.
     - Exactly one is infinite, say `z_j`: then `u_j + c ≥ M − C > z_(j') + C ≥ u_(j') + c'`,
       which is impossible.
     - Both infinite: `j = j_r`, `j' = j_q` with `r ≠ q`, so
       `|u_j − u_(j')| ≥ 2C + 1 > |c − c'|`, which is impossible.

  So `F = G` on `N` in every possible case.
- **Conclusion.** Also `N ⊆ B_0 ⊆ dom φ ∩ dom ψ`. Hence `φ = ψ` on `N`. ∎

*Remark.* In case 3, the constraint `x_j ≥ M` in `N` separates the germ at `z` from nearby
constant values. In case 5, the spacing of the `v_r` does the same job. The example
`z_0 = z_1 = ∞` with `τ` versus `id` is case 5 with both coordinates infinite. It is exactly why
`𝒢` is not Hausdorff, and exactly what the distinct values `v_r` defeat.

## 3. Minimality

Let `x ∈ X` and let `B` be a nonempty box with constraints on coordinates in `[−R, R]`. Choose
finite values `w_(−R), ..., w_R` satisfying the constraints: `n` for `{n}` or `[n, ∞]`, and `0`
for an unconstrained coordinate. Put

`φ = S^R ∘ (s_2^(w_(−R)) s_1) ∘ (s_2^(w_(−R+1)) s_1) ∘ ... ∘ (s_2^(w_R) s_1) ∈ Σ`.

It is defined on all of `X`. Each block `s_2^w s_1` pushes the current contents of coordinates
`≥ 0` one step right and writes `w` at coordinate 0. After the `2R + 1` blocks, coordinates
`0, ..., 2R` hold `w_(−R), ..., w_R`. `S^R` then moves them to `−R, ..., R`. So `φ(x) ∈ B`,
every orbit is dense, and `𝒢` is minimal.

## 4. No singular functions, and simplicity

Let `0 ≠ f = Σ_(i=1)^r a_i 1_([φ_i, U_i])` and `f(γ) ≠ 0` with `γ = [ψ, z]`.
- Apply Lemma 2 to `z`, the family `Φ = {ψ} ∪ {φ_i : z ∈ U_i}`, and the neighbourhood `O`
  given by the intersection of the `U_i` containing `z` and the complements of those not
  containing `z`.
- For `x ∈ V`, the index set `{i : x ∈ U_i, [φ_i, x] = [ψ, x]}` equals the one at `z`.
  So `f([ψ, x]) = f(γ) ≠ 0` on the open bisection `[ψ, V]`, which is a nonempty open subset of
  the support.

Every nonzero `f` therefore has support with nonempty interior. By §0 and §3, `𝒢` is a second
countable ample groupoid with Hausdorff unit space that is minimal and effective. By
`cepss-nonhausdorff-steinberg-simplicity` (S) (CEPSS, `thm:simple`), `A_K(𝒢)` is simple for
every field `K`.

## 5. Centre

Let `ζ ∈ Z(A)`.
- **Supported on isotropy.** For clopen `U ⊆ X`,
  `(1_U ζ)(γ) = 1_U(r(γ)) ζ(γ)` and `(ζ 1_U)(γ) = ζ(γ) 1_U(s(γ))`. Clopens separate points, so
  `ζ(γ) ≠ 0` forces `r(γ) = s(γ)`.
- **Supported on units.** Let `ζ(γ) ≠ 0` with `γ = [ψ, z]`, and write `ζ` as a combination of
  `1_([φ_i, U_i])`. Apply Lemma 2 to `Φ = {ψ, id} ∪ {φ_i : z ∈ U_i}` and the `O` of §4.
  - For `x ∈ V` we have `ζ([ψ, x]) = ζ(γ) ≠ 0`, so `[ψ, x]` is isotropy, and `ψ(x) = x` for all
    `x ∈ V`.
  - Hence `[ψ, x] = [id, x]` on `V`. By (D), `[ψ, z] = [id, z]`, so `γ` is a unit.
- **Invariant.** So `ζ` is a function on `X`. For `φ ∈ Σ`, put `t = 1_([φ, dom φ])`. Then
  `t ζ t* = ζ t t* = ζ 1_(ran φ)`, and evaluating at a unit `x ∈ ran φ` gives
  `ζ(φ^(-1)(x)) = ζ(x)`. So `ζ` is constant on `Σ`-orbits.
- **Constant.** Pick any `z`, and let `c = ζ(z)`. Applying Lemma 2 as in §4 gives a nonempty
  open `V` with `ζ = c` on `V`. By minimality every orbit meets `V`, so `ζ ≡ c` on `X`, and
  `ζ = c · 1_X = c · 1`.

Hence `Z(A) = K`.

## 6. Finite generation

Let `A_0` be the subalgebra generated by the 7 elements.
- `A_0` contains `1_([φ])` for every `φ ∈ Σ`, as a product of generators.
- It contains `1_({x_0 = 0}) = s_1 s_1*`, `1_({x_0 ≥ n}) = s_2^n s_2^(*n)` and
  `1_({x_0 = n}) = s_2^n s_1 s_1* s_2^(*n)`.
- Conjugating by `S^(±j)` moves these to coordinate `j`.
- Products give all boxes. Every clopen subset of `X` is a finite disjoint union of boxes, since
  the clopens of `αN` are the finite subsets of `N` and their complements. A disjoint union is a
  sum, so `A_0` contains `1_U` for every clopen `U`.
- Therefore `A_0` contains `1_([φ, U]) = 1_([φ]) 1_U`, which span `A`.

Over `F_2` no scalars are needed, so the 7 elements generate `A` as a ring.

## 7. The swindle

- **The endomorphism.** `ι([φ, x], n) = [σ(φ), h(x, n)]` defines a map from `𝒢 × αN` to `𝒢`,
  where `αN` is viewed as a trivial groupoid. It is well defined and injective, because `h` is a
  homeomorphism and `σ(φ) = h(φ × id)h^(-1)`. It is a continuous open groupoid homomorphism,
  mapping `[φ, U] × W` onto `[σφ, h(U × W)]`, and its unit map is the homeomorphism `h` onto `X`.
  Its image `𝓗` is an open subgroupoid containing all units. So extension by zero,
  `A_K(𝓗) -> A_K(𝒢)`, is a unital homomorphism: factorizations of `γ ∈ 𝓗` into factors in `𝓗`
  are the same in `𝓗` and in `𝒢`.
- **Definition of σ on A.** Put `σ(f) = ι_*(f ⊗ 1)`, where `(f ⊗ 1)(γ, n) = f(γ)`. This is a
  unital endomorphism with `σ(1_([φ, U])) = 1_([σφ, h(U × αN)])`.
- **Generator formulas.** These are the formulas for `σ(s_1), σ(s_2), σ(S), σ(τ)` in the target.
  They are checked coordinate by coordinate. For example, `σ(S)(y)` has
  `σ(S)(y)_(−1) = y_1`, `σ(S)(y)_0 = y_0`, and `σ(S)(y)_i = y_(i+1)` otherwise, which is `S τ`.
- **Swindle identity.** Split `1 = δ_0 + 1_([1, ∞])` on `αN`. For `f = 1_([φ, U])`:
  - `ι_*(f ⊗ δ_0) = 1_([σφ, s_1 U])`, since `h(x, 0) = s_1 x`. This equals
    `s_1 f s_1* = 1_([s_1 φ s_1^(-1), s_1 U])`, because `σφ(s_1 x) = s_1 φ x`.
  - `ι_*(f ⊗ 1_([1, ∞])) = 1_([σφ, h(U × [1, ∞])])`. This equals
    `s_2 σ(f) s_2* = 1_([s_2 σφ s_2^(-1), s_2 h(U × αN)])`, because `s_2 h(x, n) = h(x, n + 1)`
    and `σφ(h(x, n + 1)) = h(φ x, n + 1)`.

  Both sides are linear in `f`, so `σ(a) = s_1 a s_1* + s_2 σ(a) s_2*` holds on all of `A`.
  Together with §0 this is a Cuntz swindle structure. ∎
