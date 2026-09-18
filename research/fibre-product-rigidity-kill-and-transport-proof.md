---
rg: 2
id: fibre-product-rigidity-kill-and-transport-proof
kind: route
title: Mirror Ledrappier's shift; each layer has one-sided configurations on one side only, the fibre product has them on both sides, so the antipodal wall theorem applies; rules are killed by the same one-sided configurations, which blocks the transport closure
target: quantum-rigidity-is-not-closed-under-fibre-products
requires:
  - permutive-triangle-sfts-are-quantum-rigid
  - antipodal-one-sided-group-shift-configurations-are-walls
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
---

Notation as in the target. Write `t = (a, b) ∈ Z²` and `σ(a, b) = (−a, b)`.

## Step 1. Both layers are rigid

- **`Z`.** The rule `z(t) + z(t+e_1) + z(t+e_2) = 0` is linear with unit coefficients, so any two of
  `z(t), z(t+e_1), z(t+e_2)` determine the third. By `permutive-triangle-sfts-are-quantum-rigid`,
  item 1, `Z` is `D`-rigid for every `D ≥ 1` over every field.
- **`Y`.** We have `y ∈ Y` iff `y ∘ σ ∈ Z`, because `σ(t + e_1) = σt − e_1` and
  `σ(t + e_2) = σt + e_2`. If `E` is a `D`-family for `Y`, then `E ∘ σ` is a `D`-family for `Z`:
  - `σ` is a group automorphism of `Z²` and an isometry of the word and sup metrics, so (Q2) is
    preserved;
  - forbidden patterns correspond under `σ`, so (Q3) is preserved.

  So `E ∘ σ` commutes, and hence `E` does.

## Step 2. One-sided configurations

- **`Y` on the east.** Put `y_+ = 0` on `{a <= 0}` and `y_+(1, b) = 1` for all `b`. For
  `a >= 2`, choose `y_+(a, 0)` freely and set `y_+(a, b+1) = y_+(a, b) + y_+(a−1, b)` in both
  directions of `b`. The rule of `Y` then holds everywhere:
  - at `t` with `a <= 0`, all three terms vanish;
  - at `(1, b)`, it reads `y(1,b) + y(1,b+1) = 0`;
  - at `a >= 2`, it is the recursion.

  So `y_+ ≠ 0`, with support in `{a > 0}`.
- **`Z` on the west.** Symmetrically, `z_− = 0` on `{a >= 0}`, `z_−(−1, b) = 1` for all `b`, and
  `z_−(a, b+1) = z_−(a, b) + z_−(a+1, b)` for `a <= −2`. So `z_− ≠ 0`, with support in `{a < 0}`.
- **No opposite configurations.** `Y` has no nonzero point supported in `{a < 0}`, and `Z` none
  supported in `{a > 0}`. For `Y`, suppose `y = 0` on `{a >= 0}`. The rule at `(0, b)` gives
  `y(−1, b) = 0`, and induction to the west gives `y = 0`. For `Z` the argument is the mirror
  image. So no single layer has an antipodal pair, which is consistent with Step 1.

## Step 3. The fibre product is not rigid (item 1)

- **Setting up the wall theorem.** `Y × Z ⊆ (F_2^2)^(Z²)` is a group shift of finite type.
  `(y_+, 0)` is a nonzero point supported in `{⟨n, e_1⟩ > 0}`, and `(0, z_−)` is one supported
  in `{⟨n, e_1⟩ < 0}`.
- **Applying it.** By `antipodal-one-sided-group-shift-configurations-are-walls` with
  `v = e_1`, `Y × Z` is not `D`-wall-rigid for any `D`. Its local tiling algebras have
  noncommuting two-dimensional families, so `Y × Z` is not `D`-quantum rigid, and
  `LC(Y × Z, k) ⋊ Z²` is not finitely presented over any field.
- **Item 2.** The same argument applies verbatim to any group shifts `Y, Z` over `F_p^m`, using
  `(y, 0)` and `(0, z)`.
- **Failure of (C).** Take `Y` as base. A pattern `(y|_(pB_D), φ)` with `y ∈ Y` occurs in `Y × Z`
  iff `φ` occurs in `Z`. So a `y`-relative `D`-family is exactly a `D`-family for `Z`, and it
  commutes by Step 1. By item 3 of
  `extension-rigidity-is-base-centrality-plus-pointwise-rigidity`, non-rigidity of `Y × Z` forces
  (C_D) to fail for every `D`.

## Step 4. The transport criterion (item 3)

- **Determinism identity.** The `Z`-marginals `E^Z_c(u) = Σ_(a') E_(a',c)(u)` of a `D`-family of
  `Y × Z` form a `D`-family for `Z`. For (Q3), a ball pattern missing from `Z` pairs only with
  patterns missing from `Y × Z`; expand over the ball, where all factors commute by (Q2).
- **Rules as operator identities.** If `F` is a rule of `Z`, the ball-sum argument (Lemma 1 of
  `determinism-closure-certifies-quantum-rigidity`, which uses only (Q1)–(Q3) inside one `D`-ball)
  gives

  ```text
  E^Z_c(v) = Σ_(π ∈ L_F(c)) ∏_(f ∈ F) E^Z_(π(f))(vf),
  ```

  where `L_F(c)` is the set of patterns of `Z` on `F` that force `c`. The same holds for `Y`.
- **Claim.** For `k ∈ K`, every `E^Y(vk)` commutes with every `E^Z(v)`, for all `v`. Induct along
  the construction of `K`, for all `v` at once.
  - *Base, `k ∈ B_(2D)`.* This is (Q2).
  - *Z-step.* `E^Z(v)` is a polynomial in the `E^Z(vf)`. Each `E^Z(vf)` commutes with
    `E^Y(vk) = E^Y((vf)(f^(-1)k))` by induction, since `f^(-1)k ∈ K`.
  - *Y-step.* `E^Y(vk)` is a polynomial in the `E^Y(vkf)`. Each commutes with `E^Z(v)`, since
    `kf ∈ K`.
- **Conclusion.** If `K = Λ`, all cross pairs commute. If `Y` and `Z` are rigid, the marginals of
  each layer commute too, so every `E_(a,c)(u) = E^Y_a(u) E^Z_c(u)` commutes.

## Step 5. The example blocks the closure

- **One-sided configurations kill rules.** Translate `z_−` by `e_1`. It is then supported in
  `{a <= 0}`, it takes the value `1` at the origin, and it vanishes on `{a > 0}`. It agrees with the
  point `0` on every `F ⊆ {a > 0}` but differs from it at the origin. So `Z` has no rule inside
  `{a > 0}`. Likewise `y_+` translated by `−e_1` shows that `Y` has no rule inside `{a < 0}`.
- **Induction on the closure.** Suppose `K ⊆ {a <= 2D}` so far, and let `k` have `a(k) > 2D`.
  - A Z-step at `k` needs `f^(-1)k ∈ K`, i.e. `a(f) >= a(k) − 2D > 0`, for all `f` in some rule.
    No rule of `Z` has this property.
  - A Y-step needs `a(f) <= 2D − a(k) < 0` for all `f` in some rule of `Y`. No rule of `Y` has
    this property.

  So `K ⊆ {a <= 2D}`. `∎`

**Remark.** The kill uses nothing beyond the three required nodes and two explicit recursions.
The general mechanism is this. A nonzero configuration supported in `{⟨n, v⟩ < 0}` kills every
rule of its layer inside `{⟨n, v⟩ > 0}`, so one-sided freedom and missing rules are the same
phenomenon. The transport closure fails when the missing rules of the two layers face each other,
and the wall theorem then turns the facing freedoms into a genuine non-commuting family.
