---
rg: 2
id: epsilon-map-conjecture-gives-poincare-kernel-gd-three
kind: route
title: The Bestvina--Brady epsilon-map conjecture implies geometric dimension 3 for the Poincaré-spine kernel, by rescaled shadows and transport
target: bestvina-brady-poincare-kernel-has-geometric-dimension-three
requires:
  - bestvina-brady-epsilon-map-conjecture
  - acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear
  - acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead
artifacts:
  - research/artifacts/hl-eg-bestvina-brady-2026-09-14.md
---

Bestvina--Brady assert this implication (Remark, p. 470) without proof. This route supplies a
proof. It is a reduction: `bestvina-brady-epsilon-map-conjecture` is OPEN.

Let `L` be a flag triangulation of a spine of the Poincaré homology sphere, `G = π_1(L)` (the
binary icosahedral group, order 120), and `X`, `f`, `X_t` as in Bestvina--Brady §5 and §8.

**Step 1: bounds.** By item 1 of
`acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`, `H_L` has cohomological
dimension 2. It acts freely and cellularly on the 3-dimensional contractible cube complex `X`
(by restricting the deck action of `G_L`), so `X / H_L` is a 3-dimensional `K(H_L, 1)`, and the
geometric dimension of `H_L` is 2 or 3. Suppose it is 2. Let `Y` be a contractible 2-complex with
a free cellular `H_L`-action, and `φ: X_t → Y` an `H_L`-equivariant PL map, as in the proof of
Theorem 8.7.

**Step 2: the shadow maps are ε-maps.** Give `X_t` the length metric induced from `X`. It is an
`H_L`-invariant path metric with a free cocompact action.
- By the proof of Theorem 8.7 (p. 469), "point preimages of φ will have diameters bounded by the
  quasi-isometry constants". So every point preimage has `X_t`-diameter at most some `D`, and
  hence `X`-diameter at most `D`.
- Let `s = |f(v) − t|` and `σ: L → S_(v,L)` the homeomorphism after Definition 8.8. With `L`
  scaled to side `s`, `σ` is a quasi-isometry into `X` "with constants which are independent of
  |f(v) − t|". So `d_(L,s)(x,y) ≤ λ d_X(σx, σy) + c`, with `λ` and `c` independent of `s`.
- With the unit metric on `L`, the map `g_v = φ ∘ σ: L → K_v := φ(S_(v,L))` is surjective and PL,
  and each point preimage has diameter at most `(λD + c)/s`.
- Choosing `v` with `s` large makes `g_v` an ε-map for any prescribed ε. After subdivision, `K_v`
  is a connected finite subcomplex of `Y` (p. 470).

**Step 3: the conjecture.** By `bestvina-brady-epsilon-map-conjecture`, `K_v` is homotopy
equivalent to `M = L ∪ (1-cells) ∪ (2-cells)`, a 2-dimensional CW complex containing `L` as a
subcomplex. Only this weak form (E) is used. Choose a cellular homotopy equivalence
`h: K_v → M`.

**Step 4: transport.** Let `Z` be the pushout of `M ←h− K_v ↪ Y`.
- `K_v ↪ Y` is the inclusion of a subcomplex, hence a cofibration, and `h` is a homotopy
  equivalence. So the induced `Y → Z` is a homotopy equivalence. This is the gluing theorem for
  adjunction spaces (cobase change of a homotopy equivalence along a cofibration), recalled as
  standard and not pinned.
- `Z` is therefore contractible. It is a CW complex of dimension 2, because `h` is cellular and
  `M`, `Y` are 2-dimensional, and it contains `L ⊆ M` as a subcomplex.

**Step 5: contradiction.** `L` is a finite acyclic subcomplex of the contractible 2-complex `Z`,
with `π_1(L) = G` finite and nontrivial, hence hyperlinear. This contradicts
`acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`. So the geometric dimension of
`H_L` is 3, which is the target.

## Generality

Steps 2--5 never use `π_2(L) ≠ 0`. Let `L` be any finite acyclic flag 2-complex with nontrivial
hyperlinear `π_1(L)` for which the weak form (E) holds for the maps `g_v`. Then `H_L` has
cohomological dimension 2 and geometric dimension 3.
- Cohomological dimension 2 comes from Step 1 of `acyclic-nonaspherical-l-dichotomy-proof`, which
  uses only acyclicity and `π_1(L) ≠ 1`.
- This includes aspherical acyclic `L`, which the Bestvina--Brady dichotomy does not cover.
