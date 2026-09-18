---
rg: 2
id: almost-v-fw-germ-reduction-proof
kind: route
title: Transfix the commensurated set of V-germ classes, straighten it by one almost-V homeomorphism, and read off the germ homomorphism
target: almost-v-fw-subgroups-act-through-finitely-many-germs
requires:
  - fw-subgroups-of-eventually-similar-groups-virtually-embed
---

Notation as in the target claim: `C`, `V`, `sing`, `H`, `𝒢_y`.
Lane-proved, not independently reviewed.

## Step 0. Two facts about V

- **(V1) Fullness.** If `g in Homeo(C)` is V-local at every point, then
  `g in V`. By compactness, `C` is covered by finitely many cones on each of
  which `g` agrees with an element of `V`. Refining, `C` is partitioned into
  cones `C_{α_1}, ..., C_{α_k}` on each of which `g` is a prefix replacement
  `α_i ζ -> β_i ζ`. The images `C_{β_i}` partition `C` because `g` is a
  bijection, so `g in V`.
- **(V2) Clopen transitivity.** Two nonempty clopen sets `K, K' ⊆ C` admit a
  bijection that is locally in `V`. Each is a finite disjoint union of cones,
  and a cone `C_α` splits as `C_{α0} ⊔ C_{α1}`, so both can be written with the
  same number of cones. Map cone to cone by prefix replacement.

## Step 1. The E-set of V-germ classes

On pairs `(g, x)` with `g in H` and `x in C`, put `(g, x) ~ (g', x')` when
`g(x) = g'(x')` and `g'^-1 g` is V-local at `x`. Composites and inverses of
V-germs are V-germs, so `~` is an equivalence relation.

- Let `W` be the quotient and `T : W -> C`, `[g, x] -> g(x)`.
- `H` acts on `W` by `k·[g, x] = [kg, x]`. This is well defined because
  `(kg')^-1 (kg) = g'^-1 g`, and `T(k·w) = k T(w)`.
- Put `W_y = T^-1(y)`. Then `k W_y = W_{k(y)}`.
- Let `M = {[v, x] : v in V}`. Any two V-classes with the same target are
  equivalent, and `[id, y]` has target `y`. So `M ∩ W_y` is a single element
  `triv_y`.

**M is commensurated by H.** `k·triv_y = [kv, x]` with `v(x) = y`. It lies in
`M` iff `v'^-1 k v` is V-local at `x` for some `v' in V`, that is, iff `k` is
V-local at `y`. Hence

    kM \ M = {k·triv_y : y in sing(k)},   M \ kM = {triv_{k(y)} : y in sing(k)},

so `|kM Δ M| <= 2|sing(k)| < ∞`.

## Step 2. Transfix

`Γ` has FW, so there is a `Γ`-invariant `M' ⊆ W` with `M Δ M'` finite. Put

    F = {y in C : |M' ∩ W_y| ≠ 1},   B = {y ∉ F : M' ∩ W_y ≠ {triv_y}}.

Both lie in the finite set `T(M Δ M')`. Since `γ M' = M'` and `γ W_y = W_{γy}`,
`γ` maps `M' ∩ W_y` bijectively onto `M' ∩ W_{γy}`. So `F` is `Γ`-invariant.
Let `s(y)` be the unique element of `M' ∩ W_y` for `y ∉ F`. Then

    (E1)   γ·s(y) = s(γ y)    for all γ in Γ, y ∉ F,

and `s(y) = triv_y` for `y ∉ F ∪ B`.

`Γ` permutes the finite set `F`. Let `Γ_0` be its pointwise stabilizer, of
finite index.

## Step 3. Straighten the section

For `y in B` choose a representative `s(y) = [e_y, x_y]`, with `e_y in H` and
`e_y(x_y) = y`.
- Replacing `(e_y, x_y)` by `(e_y v, v^-1 x_y)` for `v in V` does not change the
  class. `V`-orbits are infinite, so the `x_y` can be chosen distinct.
- Choose pairwise disjoint clopen neighbourhoods `U_y ∋ x_y`, avoiding the
  finite sets `sing(e_y) \ {x_y}`, with the clopen images `e_y(U_y)` pairwise
  disjoint. Keep both complements nonempty.

Define `h = e_y` on each `U_y`. On `C \ ⋃ U_y`, let `h` be a bijection onto
`C \ ⋃ e_y(U_y)` that is locally in `V` (V2). Then `h in Homeo(C)` and
`sing(h) ⊆ {x_y : y in B}`, so `h in H`.

**Claim:** `s(y) = [h, h^-1 y]` for all `y ∉ F`.
- For `y in B`: `h^-1 y = x_y`, and `h = e_y` near `x_y`.
- For `y ∉ F ∪ B`: `h^-1 y` is not any `x_{y'}`, so `h` is V-local at `h^-1 y`.
  Then `[h, h^-1 y]` is the V-class at `y`, which is `triv_y = s(y)`.

## Step 4. Read off locality

Let `γ in Γ` and `y ∉ F`, and put `a = h^-1 y`. By (E1) and Step 3,
`[γh, a] = γ·s(y) = s(γy) = [h, h^-1 γ y]`. By definition of `~` this says
`h^-1 γ h` is V-local at `a`. Every point outside `h^-1(F)` is such an `a`, so
`h^-1 γ h` is V-local off `h^-1(F)`.

Now let `γ in Γ_0` have trivial germ at every `y in F`. Then `h^-1 γ h` has
germ `[h^-1]_y [γ]_y [h]_{h^-1 y} = 1` at each point of `h^-1(F)`, so it is
V-local everywhere. By (V1), `h^-1 γ h in V`. This proves part 1.

## Step 5. Kazhdan inputs

Suppose `Γ` is infinite with property (T). By Step 3 of the proof route of
`fw-subgroups-of-eventually-similar-groups-virtually-embed` (Delorme--Guichardet:
(T) gives (FH), which gives FW), `Γ` has FW, so part 1 applies.

Suppose every coordinate of `φ` had finite image. Then `N = ker φ` has finite
index in `Γ`. Finite-index subgroups of Kazhdan groups are Kazhdan
(Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Theorem 1.7.1), so `N`
has FW. `h^-1 N h` is an FW subgroup of `V`. Part 2 of
`fw-subgroups-of-eventually-similar-groups-virtually-embed` applies to the
Higman--Thompson group `V = V_{2,1}`, so `h^-1 N h` is finite. Then `Γ` is
finite, a contradiction. So some `y in F` has infinite image `[Γ_0]_y`, and
`F` is nonempty.

For `E <= H` containing `Γ`, `[Γ_0]_y ⊆ (E)_y` because `Γ_0` fixes `y`. ∎
