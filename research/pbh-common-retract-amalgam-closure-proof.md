---
rg: 2
id: pbh-common-retract-amalgam-closure-proof
kind: route
title: Embed the fibre product X x_C Y in a simple MIF group H, send both kernels to transvections of one letter and C to twisted conjugations in Aut_H(H * F_2), then induct over trees and vertices
target: pbh-class-closed-under-common-retract-amalgams
requires:
  - boone-higman-type-a-class-closed-under-finite-extensions
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - relative-automorphism-of-fp-simple-mif-group-has-type-a-action
  - type-a-action-gives-boone-higman-for-subgroups
---

Automorphisms compose right to left. `B_A` is as in the target. Full details, with
the same numbering, are in §§2--4 of
`research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md`.

## Step 0. Structure of G = X *_C Y

- Let `r_X: X -> C` and `r_Y: Y -> C` be retractions, with `L = ker r_X` and
  `M = ker r_Y`. So `X = L ⋊ C` and `Y = M ⋊ C`. Write `c·l = c l c^-1` in `X` and
  `c·m = c m c^-1` in `Y`.
- `r_X` and `r_Y` agree on `C`, so they glue to `R: G -> C` with `R|_C = id`.
- `N = <L, M>` is normal: `L` and `M` normalize it, and `C` normalizes `L` and `M`.
  `G = N C`, `N <= ker R`, and `ker R ∩ C = 1`. So `ker R = N` and `G = N ⋊ C`.
- `N ≅ L * M`. A reduced alternating product of nontrivial elements of `L` and `M`
  alternates between `X \ C` and `Y \ C`, since `L ∩ C = 1 = M ∩ C`. By the normal
  form theorem for amalgamated products it is nontrivial.

So `G = (L * M) ⋊ C`, with `C` acting on `L` through `X` and on `M` through `Y`.

## Step 1. The envelope

- Let `D = {(x, y) ∈ X × Y : r_X(x) = r_Y(y)}`. It contains `L × 1`, `1 × M` and
  `C_Δ = {(c, c)}`.
- In `D`: `(c, c)(l, 1)(c, c)^-1 = (c·l, 1)` and `(c, c)(1, m)(c, c)^-1 = (1, c·m)`.
- Let `Γ_X ⊇ X` and `Γ_Y ⊇ Y` carry type (A) actions. By
  `boone-higman-type-a-class-closed-under-finite-extensions`, the group
  `Γ_X × Γ_Y ∈ B_A`, so it lies in some `A_0` with a type (A) action. `A_0` is
  finitely presented, so finitely generated.
- By (i) ⟹ (iv) of BFFHZ Theorem C (`fp-simple-highly-transitive-groups-satisfy-pbh`),
  `A_0` embeds in a finitely presented simple MIF group `H`. So does `D`.
- Identify `L`, `M` and `C` with `L × 1`, `1 × M` and `C_Δ` inside `H`. Then, for all
  `c ∈ C`, `l ∈ L`, `m ∈ M`:

```text
c l c^-1 = c·l  and  c m c^-1 = c·m  in H.                                (F)
```

## Step 2. The actor and its elements

- Put `P = H * F(x, y)` and `Ω = Aut_H(P)`. By BFFHZ Theorem E
  (`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`, `n = 2`), `Ω`
  admits an action of type (A), so every subgroup of `Ω` lies in `B_A`.
- **Transvections.** For `a ∈ H * <y>`, `ρ_a` fixes `H` and `y` and sends `x -> x a`.
  - `ρ_a ρ_b(x) = ρ_a(x b) = x a b`, so `a -> ρ_a` is a homomorphism.
  - It is injective, because `ρ_a(x) = x a`.
- **Twisted conjugations.** For `c ∈ H`, `γ_c` fixes `H` and sends `x -> x c`,
  `y -> c^-1 y c`.
  - `γ_c γ_d(x) = x c d` and `γ_c γ_d(y) = (cd)^-1 y (cd)`, so `c -> γ_c` is a
    homomorphism `H -> Ω`.
  - `γ_c` preserves `H * <y>`.
- **Conjugation formula.** For `a ∈ H * <y>`:

```text
γ_c ρ_a γ_c^-1 = ρ_(c γ_c(a) c^-1).                                      (GP1)
```

  - On `x`: `x -> x c^-1 -> x a c^-1 -> x c γ_c(a) c^-1`.
  - On `y`: `γ_c^-1(y) = c y c^-1`, which `ρ_a` fixes and `γ_c` sends back to `y`.

## Step 3. The homomorphism Φ: G -> Ω

- Let `w: L * M -> H * <y>` be `l -> y l y^-1`, `m -> m`. Put `Φ_N = ρ ∘ w` and
  `Φ_C(c) = γ_c`. Both are homomorphisms.
- **The semidirect relation.** We need `γ_c ρ_(w(n)) γ_c^-1 = ρ_(w(c·n))`. By (GP1)
  the left side is `ρ_(c γ_c(w(n)) c^-1)`. The maps `n -> c γ_c(w(n)) c^-1` and
  `n -> w(c·n)` are homomorphisms, so compare them on generators.
  - `l ∈ L`: `c γ_c(y l y^-1) c^-1 = c (c^-1 y c) l (c^-1 y^-1 c) c^-1 = y (c l c^-1) y^-1`,
    which is `y (c·l) y^-1` by (F).
  - `m ∈ M`: `c γ_c(m) c^-1 = c m c^-1 = c·m` by (F).

So `Φ(n c) = ρ_(w(n)) γ_c` defines a homomorphism on `(L * M) ⋊ C = G`.

## Step 4. Injectivity

- **`w` is injective.** Take a reduced alternating word in `L \ 1` and `M \ 1`.
  - Its image is obtained by replacing each `l` with the three syllables
    `y · l · y^-1`, and keeping each `m`.
  - Two `L`-syllables are separated by an `M`-syllable, so no two `y`-letters are
    adjacent. Each `l` sits between `y` and `y^-1`, so no two `H`-letters are
    adjacent.
  - All `H`-letters are nontrivial, because `D -> H` is injective.
  - So the image is a reduced word of positive length in `H * <y>`, hence nontrivial.
- **`Φ` is injective.** Suppose `ρ_(w(n)) γ_c = id`.
  - On `y` it gives `c^-1 y c = y` in `P`. A nontrivial element of `H` does not commute
    with `y` in a free product, so `c = 1`.
  - Then `ρ_(w(n)) = id`, so `w(n) = 1`, and `n = 1`.

Hence `G <= Ω` and `G ∈ B_A`. This is Part 1.

## Step 5. Trees of groups (Part 2)

- **Lemma.** In a finite tree of groups whose edge groups are retracts of both
  adjacent vertex groups, every vertex group `G_v` is a retract of `G_S`, for every
  subtree `S ∋ v`.
  - *Proof.* Induct on `|S|`. Choose a leaf `w ≠ v` of `S`, joined by `f` to `z`, and
    put `S' = S \ w`. Then `G_S = G_S' *_(C_f) G_w`.
  - Take a retraction `ψ: G_S' -> G_v` by induction. Use `ψ` on `G_S'` and
    `ψ ∘ r_(w,f)` on `G_w`. They agree on `C_f`, so they glue to a retraction
    `G_S -> G_v`.
- **Induction on vertices.** Choose a leaf `u` joined by `e` to `v`, and let
  `T' = T \ u`. Then `G_T = G_T' *_(C_e) G_u`.
  - `C_e` is a retract of `G_u`.
  - `C_e` is a retract of `G_T'`: compose the lemma's retraction `G_T' -> G_v` with
    `r_(v,e)`.
  - `G_T' ∈ B_A` by induction. Part 1 gives `G_T ∈ B_A`.

## Step 6. Equivariant graph products (Part 3)

`C` acts on `G_Γ` because the vertex-wise actions preserve every defining relator. For
an induced subgraph `Λ`, killing `G_u` for `u ∉ Λ` gives a `C`-equivariant retraction
`G_Γ -> G_Λ`: relators go to relators or to 1. So `G_Λ ⋊ C` is a retract of
`G_Γ ⋊ C`.

- **Splitting.** For a vertex `v`,
  `G_Γ = G_(Γ \ v) *_(G_(lk v)) G_(st v)`, since the two presentations agree.
  - When `C` preserves `A`, `A'` and `B`, one has
    `(A *_B A') ⋊ C = (A ⋊ C) *_(B ⋊ C) (A' ⋊ C)`. Both sides are generated by `A`,
    `A'` and `C`, with the relations of the factors, the identification of `B`, and
    `c g c^-1 = c·g` for `g ∈ A ∪ A'`.
  - Hence `G_Γ ⋊ C = (G_(Γ \ v) ⋊ C) *_(G_(lk v) ⋊ C) (G_(st v) ⋊ C)`.
- **Stars.** `G_(st v) ⋊ C = (G_(lk v) × G_v) ⋊ C` embeds in
  `(G_(lk v) ⋊ C) × (G_v ⋊ C)` by `(g h, c) -> ((g, c), (h, c))`.
  - It is a homomorphism, because `G_(lk v)` and `G_v` commute and `C` preserves both.
  - It is injective by comparing coordinates.
- **Induction on `|V(Γ)|`.** A single vertex is the hypothesis. Otherwise:
  - `X = G_(Γ \ v) ⋊ C ∈ B_A` by induction.
  - `Y = G_(st v) ⋊ C ∈ B_A`, by the star embedding and closure under products and
    subgroups. Here `G_(lk v) ⋊ C` is in `B_A` by induction if `lk v ≠ ∅`, and is
    `C <= G_v ⋊ C` otherwise.
  - `G_(lk v) ⋊ C` is a retract of `X` and of `Y`.
  - Part 1 gives `G_Γ ⋊ C ∈ B_A`.

Every member of `B_A` embeds in a finitely presented simple group and, if finitely
generated, has solvable word problem (`type-a-action-gives-boone-higman-for-subgroups`).
