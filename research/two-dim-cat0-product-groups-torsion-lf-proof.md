---
rg: 2
id: two-dim-cat0-product-groups-torsion-lf-proof
kind: route
title: A finitely generated torsion group fixes a point in each 2-dimensional CAT(0) factor (Norin–Osajda–Przytycki) and each tree factor (Serre), so it lies in a finite point stabilizer
target: two-dim-cat0-product-groups-are-torsion-locally-finite
requires:
  - simple-kazhdan-kac-moody-lattices-exist
---

## Inputs

- **(NOP)** Norin–Osajda–Przytycki, "Torsion groups do not act on 2-dimensional CAT(0) complexes", arXiv:1902.02457v3
  (24 Jan 2022), pp. 1–3, read at source (PDF, 2026-09-18).
  - **Definition.** A *triangle complex* `X` is a 2-dimensional simplicial complex with a piecewise smooth Riemannian
    metric. The triangles containing each vertex lie in finitely many isometry classes, and `(X,d)` is a complete
    length space. This holds, for example, for an `M_κ`-complex with finitely many shapes ([BH99, I.7.13]). Groups
    act "by *automorphisms*, i.e. simplicial automorphisms that preserve the metrics `σ_T`".
  - **Corollary 1.3.** "Let `(X,d)` be a CAT(0) triangle complex. Let `G` be a finitely generated group acting on `X`
    without a global fixed point. Then `G` has an element of infinite order."
- **(Serre)** A finitely generated group acting on a tree, in which every element has a fixed point, has a global
  fixed point (Serre, *Trees*, I.6.5, Cor. 3). Cited, not re-read. It is also used in
  `circle-and-tree-product-periodic-subgroups-are-finite`.

## Item 1

Let `E ≤ Γ` be finitely generated and torsion.
- **Triangle factors.** For each `i`, `E` acts on `X_i` through `Γ → Aut(X_i)`, possibly non-faithfully. `E` has no
  element of infinite order, so by (NOP) Cor. 1.3 it has a global fixed point `x_i ∈ X_i`.
- **Tree factors.** For each `j`, every element of `E` has finite order, so it has a bounded orbit and fixes a point
  of the geometric realization of `Y_j`: a vertex, or the midpoint of an inverted edge. After subdividing, `E` acts
  without inversions and every element fixes a vertex, so by (Serre) `E` fixes a point `y_j`.
- **Conclusion.** `E` fixes `(x_1, …, x_k, y_1, …, y_l)`, so `E` lies in a finite point stabilizer and is finite.
- **Finite exponent.** A group of finite exponent is torsion. ∎

## Item 2 (Kac–Moody)

These are standard facts about twin buildings and RGD systems, cited and not read at source: Abramenko–Brown,
*Buildings*, GTM 248, Ch. 6, 8; Rémy, Astérisque 277 (2002); Caprace–Rémy, Invent. Math. 176 (2009) §1.

- **The action.** `Λ = G_A(F_q)` has a twin root datum and acts type-preservingly on its twin building
  `(Δ_+, Δ_-)` of type `(W, S)`.
- **The two realizations.** Let `X_±` be the Davis realizations: the order complexes of the posets of spherical
  residues of `Δ_±`, with Moussong's piecewise Euclidean metric. Each simplex is a Euclidean simplex whose shape
  depends only on the types of the residues in its chain.
  - There are finitely many spherical subsets, hence finitely many shapes.
  - The dimension is 2. A chain of residues has strictly nested spherical types, every spherical subset has at most
    two elements (no three generators generate a finite group), so a chain has at most three members
    (types `{s,t} ⊃ {s} ⊃ ∅`).
  - So `X_±` is a triangle complex: an `M_0`-complex with finitely many shapes, hence complete by [BH99, I.7.13] as
    cited by NOP.
  - It is CAT(0) (Davis, "Buildings are CAT(0)", LMS Lecture Notes 252 (1998); Moussong for Coxeter complexes).
  - `Λ` acts by type-preserving simplicial automorphisms, which preserve the Euclidean metrics on simplices. So it
    acts by automorphisms in the sense of (NOP).
- **Finite point stabilizers on `X_+ × X_-`.**
  - Let `x_±` lie in the relative interior of a simplex, a chain of residues. A type-preserving element fixing `x_±`
    fixes every residue of the chain, in particular its smallest one `R_±`. That is a spherical residue with finitely
    many chambers, since `q` is finite and `W_J` is finite.
  - So `Stab(x_+, x_-)` permutes the finite set of chambers of `R_+ × R_-`, and has a finite-index subgroup fixing a
    pair of chambers `(c_+, c_-)`.
  - That pair stabilizer is finite. By the twin Bruhat decomposition, after conjugation `c_+ = B_+` and
    `c_- = w B_-`. Then `Stab(c_+) ∩ Stab(c_-) = B_+ ∩ w B_- w^(−1) = T · U_(Φ_+ ∩ w Φ_-)`, with `T = T(F_q)` finite
    and `U_(Φ_+ ∩ wΦ_-)` a product of `ℓ(w)` root groups, each `≅ F_q`.
  - Equivalently, `Λ` is discrete in `Aut(X_+) × Aut(X_-)` (it is a lattice there: Rémy, Carbone–Garland; this is
    also step 1 of Rybak's chain in `fp-simple-kac-moody-lattices-are-mif`), and point stabilizers in `Aut` of a
    locally finite complex are compact.
- **Apply item 1** with `k = 2`, `l = 0`. So `Λ` is torsion locally finite.
- **Quotient by the centre.** `Z(Λ)` is finite: it lies in `T`. A finitely generated torsion subgroup of `Λ/Z(Λ)` has
  finitely generated torsion preimage (finite-by-torsion), which is finite. So `Λ/Z(Λ)` is torsion locally finite
  too.
- **The rank-3 example.** For rank 3 and irreducible, non-spherical, non-affine 2-spherical `A`, the only 3-subset is
  `S`, and `W_S = W` is infinite. So the hypothesis holds. For `Λ_(2,4,6)(q)` see (KM2) in
  `simple-kazhdan-kac-moody-lattices-exist`. ∎

## Item 3

- **Ã2 and 2-dimensional Euclidean buildings.** Chambers are Euclidean triangles or polygons of finitely many shapes,
  and the building is CAT(0) (Bruhat–Tits; Davis). Subdivide polygons into triangles equivariantly (barycentric
  subdivision), then apply item 1.
- **Fuchsian buildings.** Chambers are compact hyperbolic polygons; these are `M_{−1}`-complexes with finitely many
  shapes, CAT(−1) hence CAT(0). Subdivide, then apply item 1.
- **Scope of automorphisms.** Only automorphisms that are simplicial and isometric after the chosen subdivision are
  covered. This holds for all type-preserving automorphisms, and for all automorphisms of the barycentric
  subdivision. ∎

## Item 4

Items 1–3, applied to finitely generated subgroups. ∎
