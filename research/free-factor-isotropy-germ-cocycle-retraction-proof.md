---
rg: 2
id: free-factor-isotropy-germ-cocycle-retraction-proof
kind: route
title: The free-product germ cocycle has finite support, so finitely many relator loops present a group that retracts onto the isotropy
target: free-factor-isotropy-of-fp-full-subgroups-is-fp
requires: []
---

Notation and hypotheses (H1)–(H3) are those of the target. Fix a finite presentation
`E = <S | R>`. For each `s ∈ S` fix a finite clopen partition `X = ⊔_i U_{s,i}` and
labels `λ_{s,i} ∈ D` with `s|_{U_{s,i}} = λ_{s,i}`. Let `m` bound the free-product
length of all labels.

**Step 0. Transversal.** Every element of `D` has a unique reduced form in `A * B`. Let
`T ⊂ D` be the set of reduced words that are empty or end in a letter of `A \ 1`. Then
`T` is a transversal of `D/B`: every `d` is `t·b` with `t ∈ T`, `b ∈ B`, uniquely (strip
a final `B`-letter). By (H1), `gB ↦ g·x` is a bijection `D/B → O`. For `y ∈ O` let
`g_y ∈ T` be the representative with `g_y·x = y`, so `g_x = 1`.

For `y ∈ O` and `s ∈ S`, with `y ∈ U_{s,i}`, put `λ(s,y) = λ_{s,i}` and

    β(s, y) = g_{sy}^{-1} λ(s,y) g_y ∈ D_x = B.

Extend `λ` and `β` to words: `λ(s^{-1}, sy) = λ(s,y)^{-1}`, `β(s^{-1}, sy) = β(s,y)^{-1}`,
and multiply along the path. Then `β(uw, y) = β(u, wy) β(w, y)`, and `β(w, y)` is
unchanged by free reduction of `w`.

**Step 1. Finite support.** For fixed `λ ∈ D`, the set `{y ∈ O : g_{λy}^{-1} λ g_y ≠ 1}`
has at most `|λ| + 1` elements.

- Write `λ = ℓ_1 … ℓ_p` and `g_y = ℓ'_1 … ℓ'_q` reduced. Reduce `λ g_y`. Let `j` be the
  number of letters cancelled exactly: `ℓ_{p-i+1} = ℓ'^{-1}_i` for `i ≤ j`. If a merge
  follows, the letters `ℓ_{p-j}` and `ℓ'_{j+1}` lie in one factor, and their product is
  a nontrivial letter.
- If `j < q`, the last letter `ℓ'_q ∈ A \ 1` of `g_y` survives, or is merged into a letter
  of `A \ 1`. So the reduced form of `λ g_y` lies in `T`. It represents `λ y`, so it equals
  `g_{λy}` and the value is `1`.
- Otherwise `j = q` (this includes `y = x`). Then `g_y = (ℓ_{p-q+1} … ℓ_p)^{-1}` is fixed
  by `λ` and `q ≤ p`. That leaves at most `p + 1` points.

Each `s` has finitely many labels. So the set `E*` of Schreier edges `(y, s)` with
`β(s, y) ≠ 1` is **finite**. Let `P ⊂ O` be the finite set of their endpoints.

**Step 2. The finitely presented group `Q`.**

- **Lift.** Let `Φ` be the free group on symbols `σ_e`, one for each `e ∈ E*`. Let
  `π : Φ → B` send `σ_e ↦ β(e)`. Define the lifted cocycle `β̃` on edges: `σ_e` on
  `e ∈ E*` and `1` on the other edges, with the same inverse and path rules. Then
  `π β̃ = β`.
- **Relator words.** For `r ∈ R` and `y ∈ O`, the word `β̃(r, y)` is empty unless the path
  of `r` from `y` crosses an edge of `E*`. Each such crossing fixes `y` from a letter
  position of `r`. So the set `W` of nonempty words `β̃(r, y)` is finite.
- **`W` lies in `ker π`.** Near `y`, `r` acts as `d = λ(r, y)`. Since `r = 1` in `E`, `d`
  is the identity on a neighbourhood of `y`. So `π β̃(r, y) = β(r, y) = g_y^{-1} d g_y`
  lies in `D_x = B` and is the identity near `x`. By (H2) it is `1`.
- **Definition.** Put `Q = Φ / <<W>>`. It is finitely presented, and `π` factors
  through it.

**Step 3. A homomorphism `Ψ : St_E(x) → Q` lifting the germ.**

- **Germ map.** For `f ∈ St_E(x)`, `f` acts near `x` as some `d ∈ D` with `d x = x`,
  so `d ∈ B`. By (H2), `d` is unique. Call it `germ(f)`. This is a homomorphism, and it
  is the identity on `B ≤ E`.
- **Definition of `Ψ`.** For a word `w` of `f`, put `Ψ(f) = [β̃(w, x)]`.
- **Well defined.** Two words differ by free reductions and by a factor
  `n = Π u_i r_i^{±1} u_i^{-1}`. Each `r_i` fixes every point. The cocycle rule gives
  `β̃(u r u^{-1}, y) = β̃(u^{-1}, y)^{-1} β̃(r, u^{-1}y) β̃(u^{-1}, y)`, which lies in
  `<<W>>`. So `Ψ` is well defined. It is a homomorphism, since loops at `x` concatenate.
- **Lift.** `π Ψ(f) = β(w, x)`. The product telescopes to
  `g_x^{-1} λ(w, x) g_x = germ(f)`, because `g_x = 1`.

**Step 4. `Ψ` kills the neighbourhood kernel.**

- **Setup.** Let `ℓ ∈ E` be the identity on a neighbourhood `N` of `x`, with word `w`.
  The bad set `Z = {z ∈ O : w_j z ∈ P for some suffix w_j of w}` is finite.
- **Moving the base point.** By (H3), choose `c ∈ E` that is the identity outside `N`
  and has `c(x) = z ∉ Z`.
- **`c` commutes with `ℓ`.** `c` preserves `N`, `ℓ` is the identity on `N` and
  preserves `X \ N`, and `c` is the identity on `X \ N`. So `c^{-1} ℓ c = ℓ`.
- **Evaluation.** Let `u` be a word for `c`. Then `u^{-1} w u` is a word for `ℓ`, and
  `Ψ(ℓ) = β̃(u, x)^{-1} β̃(w, z) β̃(u, x)`. The path of `w` from `z` meets no point of
  `P`, so it crosses no edge of `E*`, and `β̃(w, z) = 1`. So `Ψ(ℓ) = 1`.

**Step 5. Retraction.**

- **Factoring through the germ.** By Steps 3–4, `Ψ` is constant on the fibres of
  `germ`. The germ map is onto `B`, since `B ≤ St_E(x)`. So `Ψ` induces
  `ψ : B → Q` with `π ψ = id_B`.
- **The kernel of `π`.** Let `q_1, …, q_n` generate `Q`, and let `M` be the normal closure
  of the elements `q_i^{-1} ψπ(q_i)`. Then `M ≤ ker π`.
- **`q ≡ ψπ(q)` modulo `M`.** This holds on generators, and both sides are homomorphisms
  of `q`. So it holds for all `q ∈ Q`.
- **Conclusion.** If `π(q) = 1`, then `q ∈ M`. So `ker π = M` is finitely normally
  generated, and `B ≅ Q/M` is finitely presented. `∎`

**Where each hypothesis is used.**
- (H1) is used in Step 0, for the bijection `D/B → O`.
- (H2) is used in Step 2, where it forces the relator words into `ker π`, and in Step 3,
  where it makes the germ unique.
- (H3) is used only in Step 4. Without it, the neighbourhood kernel can survive in `Q`,
  and no retraction is claimed. No counterexample to the (H3)-free statement is
  recorded here.
- The free-factor hypothesis is used only in Step 1. Over an amalgam `A *_C B` with
  `C ≠ 1`, a normal form carries a `C`-letter across the whole word. Then the support of
  `β` is in general infinite, and the argument stops.
