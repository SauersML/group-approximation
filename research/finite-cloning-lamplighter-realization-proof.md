---
rg: 2
id: finite-cloning-lamplighter-realization-proof
kind: route
title: "Coset-tree cloning systems: pushforward of lamps along Trees_j/H realizes every lamp stabilizer H in F"
target: finite-cloning-groups-realize-every-lamplighter-over-thompson-f
requires: []
artifacts:
  - experiments/zaremsky-2-16-lehnert-conjecture-2026-09-17/coset_tree_cloning_check.py
  - experiments/zaremsky-2-16-lehnert-conjecture-2026-09-17/coset_tree_cloning_check.out
---

Complete hand proof (unreviewed). A computer check of the axioms is in the experiment
artifact (see section 5).

## 0. Conventions

- The definitions follow Zaremsky, arXiv:1606.08762, Section 2 (= Witzel–Zaremsky,
  arXiv:1405.5491, Def. 2.18). Maps are written on the right: `(g)ι κ` means apply `ι`
  and then `κ`. The axioms are:
  - (2): `ι_{m,n} ∘ κ^n_k = κ^m_k ∘ ι_{m+1,n+1}` for `1 ≤ k ≤ m ≤ n`;
  - (C1): `(gh)κ_k = (g)κ_{ρ(h)k} (h)κ_k`;
  - (C2): `κ^n_ℓ ∘ κ^{n+1}_k = κ^n_k ∘ κ^{n+1}_{ℓ+1}` for `k < ℓ`;
  - (C3): `ρ_{n+1}((g)κ_k)(i) = ς_k(ρ_n(g))(i)` for `i ≠ k, k+1`.
- `Trees_j` is the set of rooted binary trees with `j` leaves, with leaves numbered
  left to right. For a tree `W` with `j` leaves and `1 ≤ k ≤ j`, `W c_k` is `W` with a
  caret attached to leaf `k`. Carets satisfy `W c_ℓ c_k = W c_k c_{ℓ+1}` for `k < ℓ`:
  attaching a caret to leaf `ℓ` and then to leaf `k` gives the same tree as attaching to
  `k` and then to the leaf that is now numbered `ℓ+1`.
- For `W, W' ∈ Trees_j`, `[W, W'] ∈ F` is the dyadic PL homeomorphism of `[0,1]` that
  maps the `i`-th leaf interval of `W'` affinely onto the `i`-th leaf interval of `W`,
  for every `i`. So `[W,W'][W',W''] = [W,W'']` (composition of functions, right factor
  first), `[W,W]=1` and `[W,W']^{-1} = [W',W]`. Also `[W c_k, W' c_k] = [W, W']`,
  because both halves of leaf interval `k` map affinely onto the two halves of its image.
  Every element of `F` is `[W,W']` for some `j` and some pair in `Trees_j`.

## 1. The construction

Fix a subgroup `H ≤ F` (arbitrary, not necessarily finitely generated) and a nontrivial
finite abelian group `A`.

1. **Coset trees.** On `Trees_j` put `W ~ W'` iff `[W,W'] ∈ H`. This is an equivalence
   relation, by the three identities in section 0. Let `Y_j = Trees_j/~` and write
   `[W]_j` for the class of `W`. Because `[W c_k, W' c_k] = [W, W']`, we have
   `W ~ W' ⇔ W c_k ~ W' c_k`.
2. **Index sets.** `D_n = Y_1 ⊔ Y_2 ⊔ ... ⊔ Y_n`, a finite set. Its elements are pairs
   (level `j`, class `[W]_j`).
3. **Cloning of points.** For `1 ≤ k ≤ n` define `s^n_k : D_n → D_{n+1}` by
   - `s_k([W]_j) = [W c_k]_{j+1}` if `k ≤ j`;
   - `s_k([W]_j) = [W]_j` if `j < k`.

   This is well defined by item 1. It is injective. On the levels `j ≥ k` it is injective
   by item 1, and its values there lie on the levels `≥ k+1`. On the levels `j < k` it is
   the identity, with values on the levels `< k`.
4. **Groups.** `G_n = A^{D_n}`, the functions `D_n → A` under pointwise addition. It has
   order `|A|^{|D_n|}`, so it is finite.
5. **Maps.**
   - `ι_{m,n}: G_m → G_n` is extension by zero along the inclusion `D_m ⊆ D_n`.
   - `ρ_n` is trivial (the pure case).
   - `κ^n_k : G_n → G_{n+1}` is pushforward along `s^n_k`:
     `(g)κ_k (s_k(d)) = g(d)`, and `(g)κ_k = 0` off the image `s_k(D_n)`.

   Pushforward along an injective map is an injective homomorphism.

## 2. The axioms

- **Directed system.** `ι_{n,n} = id`, `ι_{ℓ,m}ι_{m,n} = ι_{ℓ,n}`, and each `ι` is
  injective.
- **(1)** is trivial because `ρ` is trivial.
- **(2).** For `k ≤ m ≤ n`, `s^n_k` restricted to `D_m` equals `s^m_k` followed by the
  inclusion `D_{m+1} ⊆ D_{n+1}`: the formula in 1.3 does not depend on `n`.
  Pushforward is functorial, so `(g)ι_{m,n}κ^n_k = (g)κ^m_k ι_{m+1,n+1}` for
  `g ∈ G_m`.
- **Extra padding identity (WZ (2.5)).** For `m < k ≤ n`, `s^n_k` is the identity on
  `D_m`. So `(g)ι_{m,n}κ^n_k = (g)ι_{m,n+1}`. The cloning systems of the guide do not
  require this, but it holds here.
- **(C1).** With `ρ` trivial, (C1) says `κ_k` is a homomorphism. Pushforward is a
  homomorphism.
- **(C3).** `ρ_{n+1}((g)κ_k) = id = ς_k(id) = ς_k(ρ_n(g))`.
- **(C2).** By functoriality it suffices to show `s_ℓ` then `s_k` equals `s_k` then
  `s_{ℓ+1}` on points, for `k < ℓ ≤ n`. Take `[W]_j ∈ D_n`.
  - If `ℓ ≤ j`: the first composite gives `[W c_ℓ c_k]_{j+2}`. The second gives
    `[W c_k c_{ℓ+1}]_{j+2}`, since `ℓ+1 ≤ j+1`. The two trees are equal.
  - If `k ≤ j < ℓ`: `s_ℓ` fixes the point, and `s_k` then gives `[W c_k]_{j+1}`. In the
    other order, `s_k` gives `[W c_k]_{j+1}`, and `s_{ℓ+1}` fixes it since `j+1 < ℓ+1`.
  - If `j < k`: all four maps fix the point.
- **Properly graded** (guide Def. 2.2; WZ Def. 2.16). A function `g ∈ G_{n+1}` is in
  `im κ^n_k ∩ im ι_{n,n+1}` iff it is supported in `s_k(D_n) ∩ D_n`. That set is
  - the levels `< k`, together with the images of the levels `k..n-1`, when `k ≤ n-1`;
  - `D_{n-1}`, when `k = n`.

  In both cases it is `s_k(D_{n-1})`. So `g = (h̄)κ^{n-1}_k ι_{n,n+1}` with `h̄ ∈ G_{n-1}`
  supported where `g` is (with `κ^{n-1}_n := ι_{n-1,n}`, as in WZ). Then
  `h = (h̄)ι_{n-1,n}`, by injectivity of `κ^n_k`.

So `((G_n), (ι_{m,n}), (ρ_n), (κ^n_k))` is a properly graded pure cloning system on
finite groups. It depends on `H` and `A` only.

## 3. T(G_*) is a permutational lamplighter over F

Elements of `T(G_*)` are classes `[T_-, g, T_+]`, with `T_±` trees with `n` leaves and
`g ∈ G_n`. The relation is expansion, `[T_-, g, T_+] = [T_- c_k, (g)κ_k, T_+ c_k]`,
because `ρ` is trivial. The product is `[T_-, g, T_+][T_+, h, U] = [T_-, gh, U]`, after
expanding the two factors to a common middle tree.

1. **Semidirect product.** `π[T_-, g, T_+] = [T_-, T_+] ∈ F` is well defined (expansion
   preserves the tree pair's element) and is a homomorphism. It has the section
   `[T_-, T_+] ↦ [T_-, 0, T_+]`, which is well defined since `(0)κ_k = 0`. If
   `[T_-, T_+] = 1`, then the two leaf subdivisions agree, so `T_- = T_+`. Hence
   `ker π = K := {[T, g, T]} = colim_T G_{|T|}`. The colimit is over the directed set of
   trees ordered by expansion, with transition maps `κ_k`. Therefore
   `T(G_*) = K ⋊ F`, and `f = [T_-, 0, T_+]` acts by conjugation:
   `f [T_+, g, T_+] f^{-1} = [T_-, g, T_-]`.
2. **The lamp set.** Every transition map is pushforward along an injective map of sets.
   So `K = A^{(D_∞)}`, the finitely supported functions on
   `D_∞ := colim_T D_{|T|} = (⊔_T D_{|T|}) / ((T, d) ≈ (T c_k, s_k(d)))`.
   This relation generates an equivalence relation, and any two trees have a common
   expansion. `F` permutes `D_∞` by `[T_-, T_+]·(T_+, d) = (T_-, d)`, and conjugation on
   `K` is the induced permutation of coordinates. So
   `T(G_*) ≅ A^{(D_∞)} ⋊ F = A ≀_{D_∞} F`.
3. **The full orbit.** Call `(T, [W]_j)` *full* if `j = |T|` and *partial* if `j < |T|`.
   Expansion preserves each type: a full point `(T,[W]_n)` goes to `(T c_k, [W c_k]_{n+1})`,
   and a partial point stays partial. Define `Φ(T, [W]_n) = H [W, T] ∈ H\F`.
   - It is well defined: `[W c_k, T c_k] = [W, T]`, and `W ~ W'` gives
     `H[W',T] = H[W',W][W,T] = H[W,T]`.
   - It is surjective: every element of `F` is some `[W, T]`.
   - It is injective. Expand two full points to a common tree `T`. Then
     `H[W,T] = H[W',T]` gives `[W,W'] = [W,T][W',T]^{-1} ∈ H`, so `[W]_n = [W']_n`.
   - It is equivariant: `Φ(f·(T_+, [W])) = H[W, T_-] = H[W,T_+][T_+,T_-] = Φ(T_+,[W]) f^{-1}`.

   So the full points form one `F`-orbit, isomorphic to `F/H` with left multiplication
   (via `Hx ↦ x^{-1}H`). The point `p_0 := (•, [•]_1)`, where `•` is the one-leaf tree,
   has `Φ(p_0) = H`. Its stabilizer is exactly `H`.
4. **The partial orbit.** Let `q_0 := (Λ, [•]_1)`, where `Λ` is the two-leaf tree. Take
   a partial point `(T, [W]_j)` with `n = |T| > j`.
   - Let `U` be the tree with a root caret, left subtree `W` and any right subtree `R`
     with `n - j` leaves. Then `f = [U, T]` sends the point to `(U, [W]_j)`.
   - Attaching to leaf 1 of `caret(•, R)` the carets that build `W` (all at positions
     `≤` the current level) expands `(caret(•,R), [•]_1)` to `(U, [W]_j)`.
   - Carets on the leaves of `R` (positions `> 1`) fix level 1. So `(caret(•,R), [•]_1)`
     equals `(caret(•,R'), [•]_1)` after expansion, for any `R, R'` with equally many
     leaves, and these are related by an element of `F`. Starting from `R = •`, this
     reaches `q_0`.

   So `D_∞ = F·p_0 ⊔ F·q_0`: exactly two orbits.
5. **Finite generation.** `T(G_*)` is generated by `x_0`, `x_1` (as `[T_-, 0, T_+]`) and
   the lamps `a·δ_{p_0}`, `a·δ_{q_0}` for `a` in a generating set of `A`. A lamp at `p_0`
   is `[•, a, •]` with `a ∈ G_1 = A^{Y_1} = A`.
6. **Lamp stabilizer.** Let `t = [•, a, •]` with `a ≠ 0`. For `f ∈ F`, `f t f^{-1}` is
   the lamp `a·δ_{f·p_0}`. So `[t, f] = 1 ⇔ f·p_0 = p_0 ⇔ f ∈ H`. If `A = ⟨a⟩` is cyclic,
   then `⟨F, t⟩ = A^{(F/H)} ⋊ F` (the lamps in the full orbit), which is the permutational
   wreath product `A ≀_{F/H} F`.

## 4. Summary

For every `H ≤ F` and every finite abelian `A ≠ 0` there is a properly graded pure
cloning system on finite groups with `T(G_*) = A ≀_{D_∞} F`. Here
`D_∞ = F/H ⊔ F/P`, where `P = Stab(q_0)`, and `T(G_*)` is finitely generated. For cyclic `A` it
contains `A ≀_{F/H} F = ⟨x_0, x_1, t⟩`, with `C_F(t) = H`. This is the claim
`finite-cloning-groups-realize-every-lamplighter-over-thompson-f`.

## 5. Computer check

`experiments/zaremsky-2-16-lehnert-conjecture-2026-09-17/coset_tree_cloning_check.py`
checks sections 1–3 on five decidable subgroups: `1`, `F`, `{f'(0)=1}`, `Stab(1/3)` and
`{f = id on [1/2,1]}`. For each it checks:
- `~_H` is an equivalence relation, on all triples up to 5 leaves;
- `s_k` is well defined and injective, and (C2) and proper grading hold, for `n ≤ 6`;
- `f·p_0 = p_0 ⇔ f ∈ H`, computed in the colimit `D_∞`, for all 19415 tree pairs with at
  most 7 leaves;
- the intervals `x_0^i(J_0)` used in the target routes, for `i < 6`.

Output (`coset_tree_cloning_check.out`): all checks pass. The index-set sizes `|D_n|`,
`n = 1..6`, are `1,2,4,9,23,65` for `H = 1` (cumulative Catalan numbers) and `1..6` for
`H = F`.
