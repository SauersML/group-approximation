---
rg: 2
id: raag-kernel-dehn-function-below-bestvina-brady-proof
kind: route
title: The suspension of the four-vertex path has a quadratic kernel and a cubic Bestvina–Brady group
target: raag-kernel-dehn-function-below-bestvina-brady
requires:
  - bestvina-brady-dehn-function-classification
---

Notation as in the target. Dehn functions are compared up to the standard
equivalence `≃`.

**1. The kernel.** Since `Γ` is the join `{A, B} * P`, every generator in
`{A, B}` commutes with every generator of `P`, and `A_Γ = F(A, B) × A_P`.
The character is `χ(g, h) = χ_P(h)`, where `χ_P : A_P → Z` sends each of
`C, D, E, F` to `1`. It is surjective because `χ(C) = 1`, and
`K_χ = F(A, B) × ker χ_P = F(A, B) × BB_P`.

`P` is a tree, so its flag complex is a contractible 1-dimensional complex.
By Bestvina–Brady (Invent. Math. 129 (1997)), `BB_P` acts freely and
cocompactly on a level set of the height function on the universal cover of
the Salvetti complex of `A_P`. That level set is contractible (the flag complex
is contractible) and 1-dimensional (the Salvetti complex of `A_P` is
2-dimensional), so it is a tree, and `BB_P` is a free group of finite rank. It
is nontrivial, since it contains `C D^{-1}`. (The Dicks–Leary presentation,
with one generator per edge and relators only from triangles, gives rank 3;
only rank `≥ 1` is used.)

So `K_χ ≅ F_2 × F_r` with `r ≥ 1`. It is finitely presented, and it acts
freely and cocompactly on a product of two trees, a CAT(0) square complex, so
`δ_{K_χ} ≼ n^2`. It contains `Z^2 = ⟨A, C D^{-1}⟩`, so it is not hyperbolic,
and a finitely presented group with subquadratic Dehn function is hyperbolic
(Gromov; Olshanskii, Bowditch, Papasoglu). Hence `δ_{K_χ} ≃ n^2`.

**2. The Bestvina–Brady group.** The flag complex `Δ(Γ)` is the suspension of
the arc `Δ(P)`, a disc, so it is simply connected and `BB_Γ` is finitely
presented (Bestvina–Brady). `Γ` is reducible, being the join `{A, B} * P`,
so `Γ` is its own unique maximal reducible subgraph. Both factors are
irreducible and have at least two vertices:

- `{A, B}` has no edges, while a join of two nonempty graphs has an edge;
- the complement of a join of two nonempty graphs is disconnected, while the
  complement of the path `C – D – E – F` is the connected path `E – C – F – D`.

So `Γ` is essentially 2-reducible in the sense of Chang–García-Mejía–Migliorini
(arXiv:2507.07566v2, Definition 1), and its flag complex is simply connected.
By their Corollary 1 (equivalently Theorem 1 with `d(Γ) = 3`: property (D3)
holds, and (D4) fails because the only maximal reducible subgraph, `Γ`, has
simply connected flag complex), `δ_{BB_Γ} ≃ n^3`. This `Γ` is the paper's own
cubic example `Γ_1` in Figure 1, "the suspension of the path of length three
induced by the vertices C, D, E, and F".

**3. Conclusion.** `n^3 ⋠ n^2`, so `δ_{BB_Γ} ⋠ δ_{K_χ}`.

**The general family.** For `Γ = T * Λ` with `T` a tree that is not a star
and `Λ` irreducible with at least two vertices:

- `T` is irreducible, since a tree that is a join of two nonempty graphs is a
  star: two vertices on each side would span a 4-cycle.
- `Δ(Γ) = Δ(T) * Δ(Λ)` is simply connected, since `Δ(T)` is connected and
  `Δ(Λ)` is nonempty.
- `Γ` is its own unique maximal reducible subgraph, so `d(Γ) = 3` and
  `δ_{BB_Γ} ≃ n^3`.
- With `χ = 1` on `T` and `0` on `Λ`, `K_χ = BB_T × A_Λ` with `BB_T` free of
  finite rank `≥ 1`. It acts freely and cocompactly on the product of a tree
  with the universal cover of the Salvetti complex of `A_Λ`, a CAT(0) cube
  complex, so `δ_{K_χ} ≼ n^2`. It contains `Z^2` (a vertex of `Λ` with a
  nontrivial element of `BB_T`), so `δ_{K_χ} ≃ n^2`.

**Mechanism.** The cubic lower bound for `BB_Γ` comes from the interaction of
the two join factors inside one kernel. Killing a whole irreducible join
factor turns the kernel into a direct product, and the interaction disappears.
