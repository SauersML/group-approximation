---
rg: 2
id: nv-jacobian-subgroup-turing-machine-distortion-proof
kind: route
title: "Phi conjugates the Lebesgue-preserving subgroup of 2V onto the moving-tape Turing-machine group RTM_fix(2,1); import Theorem D there, then apply bounded-or-linear"
target: nv-jacobian-subgroup-contains-turing-machine-distortion
requires:
  - nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal
  - brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination
  - cubical-coset-proper-actions-capture-distorted-elements
---

Notation as in the target.

## Imports (verbatim)

A. Callard and V. Salo, *Distortion element in the automorphism group of a full shift*,
arXiv:2208.00685v2 (published in Ergodic Theory Dynam. Systems 44 (2024)). The v2 PDF was read on
2026-09-19, pp. 2, 43 and 45. The citation route `brin-thompson-mv-contains-a-distortion-element-citation`
already quotes Theorem D from p. 5 in the same words.

- **Definition of distortion (p. 2):** "If G is a finitely-generated group, we say g ∈ G is a
  distortion element, or distorted, if g is of infinite order and the word norm |g^n| grows
  sublinearly (with respect to some, or equivalently any, finite generating set). For groups that
  are not finitely-generated, we say that an element is distorted if it is distorted in some
  finitely-generated subgroup."
- **Definition 6.1 (p. 43):** "Let n ≥ 2 and k ≥ 1. Let Y_n be the full shift on n letters, and
  X_k = {x ∈ {0,1,...,k}^Z | 0 ∉ {x_i, x_j} ⟹ i = j}. Then
  RTM(n,k) = {f ∈ Aut(Y_n × X_k) | f|_{Y_n×{0^Z}} = id|_{Y_n×{0^Z}}}."
- **Theorem D (p. 43):** "Let n ≥ 2, k ≥ 1. Then the group of Turing machines RTM(n,k) contains a
  distortion element; indeed there is a finitely-generated subgroup G = ⟨F⟩ and an element f such
  that |f^n|_F = O(log^4 n)."
- **Definition 6.2 (p. 45):** "Write RTM_fix(n,k) for the family of homeomorphisms
  f : ⟦k⟧ × ⟦n⟧^Z → ⟦k⟧ × ⟦n⟧^Z such that for some radius r ≥ 1 and local rule
  f_loc : {0,1}^r × {0,1}^r × ⟦k⟧ → {0,1}^* × {0,1}^* × ⟦k⟧ we have
  f(xu.vy, a) = (xu′.v′y, b) whenever f_loc(u,v,a) = (u′,v′,b) and for all u,v,
  f_loc(u,v) = (u′,v′,n) satisfies |u′| + |v′| = 2r."
  (The alphabet `{0,1}` in the local rule is the paper's; for general `n` it should read `⟦n⟧`.
  We use only `n = 2`, where `⟦2⟧ = {0,1}` and there is no ambiguity.)
- **Lemma 6.3 (p. 45):** "The family of homeomorphisms RTM_fix(n,k) forms a group under
  composition, and there is a canonical group isomorphism RTM_fix(n,k) ≅ RTM(n,k)."

Lemma 6.4 (the embedding of `RTM(n,k)` into `mV`) is **not** used.

## Step 1 (identification, item 1)

Take `n = 2`, `k = 1`. Then `⟦1⟧` is a point, the state never changes, and `RTM_fix(2,1)` is the
set of homeomorphisms `f` of `X = {0,1}^Z` for which there are `r ≥ 1` and a rule
`(u, v) ↦ (u′, v′)` on `{0,1}^r × {0,1}^r` with `|u′| + |v′| = 2r` and
`f(… x u . v y …) = … x u′ . v′ y …`. The point marks the gap between positions `−1` and `0`.

**Cylinders.** As in the proof of item 3(b) of the Jacobian node
(`nv-cocycle-kernel-jacobian-diagonal-split-proof`), `Φ(a,b)_i = a_i` for `i ≥ 0` and
`Φ(a,b)_i = b_{−1−i}` for `i < 0`. So for words `u, v`, with `ū` the reversal of `u`,
```text
Φ([v] × [ū]) = [u . v]     (the cylinder with u on positions [−|u|, 0) and v on [0, |v|)).
```
For `x = Φ(v a, ū b)` we have `x = … b_1 b_0 u . v a_0 a_1 …`. The map
`(v a, ū b) ↦ (v′ a, ū′ b)` is the prefix replacement `[v]×[ū] → [v′]×[ū′]`. Under `Φ` it becomes
`… b_1 b_0 u . v a_0 … ↦ … b_1 b_0 u′ . v′ a_0 …`, with the new point placed between `u′` and `v′`.
That is exactly the moving-tape rule `xu.vy ↦ xu′.v′y`. Its Jacobian on the brick is
`(|v′| + |ū′|) − (|v| + |ū|) = |u′| + |v′| − |u| − |v|`.

**`Φ^{-1} RTM_fix(2,1) Φ ⊆ M_2`.** Let `f` have radius `r` and rule `f_loc`.
- The bricks `[v]×[ū]`, over `(u, v) ∈ {0,1}^r × {0,1}^r`, partition `C^2`.
- On each of them `Φ^{-1} f Φ` is the prefix replacement onto `[v′]×[ū′]`.
- `Φ^{-1} f Φ` is a homeomorphism, so the image bricks are pairwise disjoint and cover `C^2`.

So `Φ^{-1} f Φ ∈ 2V`, with Jacobian `|u′| + |v′| − 2r = 0` on every brick of this table. By item
3(a) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal` it lies in `M_2`.

**`Φ M_2 Φ^{-1} ⊆ RTM_fix(2,1)`.** Let `g ∈ M_2` have table bricks `[p]×[q] → [p′]×[q′]`, with
`|p′| + |q′| = |p| + |q|` on each (item 3(a)). Choose `r ≥ max(|p|, |q|, 1)` over the table.
- Subdivide each brick into the bricks `[p w]×[q w′]` with `|p w| = |q w′| = r`.
- `g` maps each of these by prefix replacement onto `[p′ w]×[q′ w′]`, where
  `|p′ w| + |q′ w′| = |p′| + |q′| + 2r − |p| − |q| = 2r`.
- The bricks `[pw]×[qw′]` run over all of `{0,1}^r × {0,1}^r`, each once.

Put `v = pw` and `ū = qw′`. Define `f_loc(u, v) = (u′, v′)` with `v′ = p′w` and `ū′ = q′w′`. The
lengths satisfy `|u′| + |v′| = 2r`. By the cylinder computation, `f = Φ g Φ^{-1}` satisfies
`f(xu.vy) = xu′.v′y` for all `x, y`, and `f` is a homeomorphism. So `f ∈ RTM_fix(2,1)`.

The two inclusions give `Φ M_2 Φ^{-1} = RTM_fix(2,1)`. Conjugation by `Φ` is a group isomorphism,
so Lemma 6.3 gives `M_2 ≅ RTM_fix(2,1) ≅ RTM(2,1)`. This proves item 1.

## Step 2 (distortion, item 2)

- By Theorem D with `n = 2`, `k = 1`, and the definition on p. 2, `RTM(2,1)` has a finitely
  generated subgroup `⟨F⟩` and an element `f_0` of infinite order with
  `|f_0^N|_F = O(log^4 N)`. (Theorem D states `f ∈ ⟨F⟩` implicitly, since `|f^n|_F` is a word norm
  in `⟨F⟩`.)
- Transport through the isomorphism of Step 1 to get `L_2 = ⟨F_2⟩ ≤ M_2` and `f_2 ∈ L_2`. A group
  isomorphism preserves order and carries word norms to word norms.
- For `n ≥ 3`, item 3(d) of the Jacobian node says `g ↦ g × id` maps `M_2` into `M_n`. It is an
  injective homomorphism, since `(g × id)(x, y) = (gx, y)`. So `L = L_2 × id ≤ M_n` and
  `f = f_2 × id` have the same properties. For `n = 2` take `L = L_2`, `f = f_2`.

`K` is a directed union of finite groups (`brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination`,
Setting: `K = ⋃_m K_m` with `K_m` finite). So every element of `K` has finite order, and `f ∉ K`.
Suppose `f^d ∈ D` with `d ≥ 1`. Then `f^d ∈ M_n ∩ D = K` (item 1 of the Jacobian node), so `f^d`
has finite order, and so does `f`. That is a contradiction. This proves item 2.

## Step 3 (class-kill, item 3)

Let `M_n` act on a set `E` commensurating `A ⊆ E`, and put `ℓ(g) = |gA Δ A|`.
- By Step 0 of `cubical-coset-proper-actions-capture-distorted-elements-proof`, `ℓ` is subadditive
  and `ℓ(g) ≤ κ|g|_L` on `L`, with `κ = max_{s ∈ F} ℓ(s)`. So `ℓ(f^N) = O(log^4 N) = o(N)`.
- By item 1 (bounded-or-linear) of `cubical-coset-proper-actions-capture-distorted-elements`,
  `|ℓ(f^N) − mN| ≤ C` with `m ∈ Z_{≥0}`. Sublinearity forces `m = 0`, so `ℓ(f^N) ≤ C` for all
  `N ≥ 0`.
- The `f^N` are pairwise distinct, because `f` has infinite order. So `{ℓ ≤ C}` is infinite, and
  `ℓ` is not proper.

(This is item 3 of that claim with `G = M_n` and `H = 1`.) A commensurating action of `nV`
restricts to one of `M_n`, and actions on CAT(0) cube complexes and discrete wall spaces are
commensurating actions, as recorded in the Setting of that claim. This proves item 3.

## Step 4 (forced shape, item 4)

Let `ψ` be cnd on `nV` with `ψ(1) = 0`. Subtracting the constant `ψ(1)` preserves being cnd, and
the conditions `Σ a_i = 0` in the definition annihilate constants, so this normalisation costs
nothing.
- The kernel `(g, h) ↦ ψ(h^{-1} g)` is conditionally of negative type. Schoenberg's theorem gives
  a map `g ↦ v_g` into a real Hilbert space with `‖v_g − v_h‖² = ψ(h^{-1} g)`.
- So `d(g, h) = ψ(h^{-1} g)^{1/2}` is a left-invariant pseudometric, and
  `ψ(gh)^{1/2} ≤ ψ(g)^{1/2} + ψ(h)^{1/2}`.
- Hence `ψ(f^N)^{1/2} ≤ κ′ |f^N|_L` with `κ′ = max_{s ∈ F} ψ(s)^{1/2}`, and
  `ψ(f^N) = O(log^8 N)`.

If `ψ` is proper on `M_n`, then each sublevel set meets `{f^N}` in finitely many elements, so
`ψ(f^N) → ∞`. This proves item 4.

For the Maharam function `ψ_M(g) = ∫|c(g)(x)_1| dλ(x)` on `M_n` (item 6(c) of the Jacobian node),
the cocycle identity gives
```text
ψ_M(gh) = ∫|c(g)(hx)_1 + c(h)(x)_1| dλ ≤ ψ_M(g) + ψ_M(h),
```
using `h_*λ = λ`. So `ψ_M(f^N) = O(log^4 N)`, as stated in the target's "Why it matters".

## Step 5 (items 5 and 6)

Item 5 combines item 3 here with items 5 and 6(a) of `nv-cocycle-kernel-is-jacobian-kernel-meet-diagonal`.
Item 6 is the route `turing-machine-group-rtm-2-1-a-t-menable-from-nv`, together with item 1
here and item 3(c) of the Jacobian node for `[[X]] ≤ M_2`. ∎
