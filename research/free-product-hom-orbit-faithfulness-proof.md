---
rg: 2
id: free-product-hom-orbit-faithfulness-proof
kind: route
title: Substitute t for x_1 and use that free products are mixed-identity-free
target: free-product-hom-orbits-of-relative-automorphisms-are-faithful
requires:
  - baumslag-gersten-group-is-highly-transitive-and-mif
---

Notation as in the target. Write `φ·α = φ ∘ α` for the precomposition action.

**Input (MIF of free products).** Let `S ≠ 1` and `k ≥ 1`. The free product
`Q = S * F(t_1, ..., t_k)` is not virtually cyclic, so it is acylindrically hyperbolic,
and a nontrivial free product other than `Z/2 * Z/2` has no nontrivial finite normal
subgroup. By Hull–Osin (arXiv:1501.04182, the corollary labelled `ah-mif`, read at
source by lane bh-free-35 and recorded in
`baumslag-gersten-group-is-highly-transitive-and-mif`), `Q` is MIF. That is, for every
`m ≥ 1`, a word `w ∈ Q * F(y_1, ..., y_m)` with `w(g) = 1` for all `g ∈ Q^m` is trivial.

**Step 1 (a large piece of the orbit).** Let `g = (g_2, ..., g_n) ∈ Q^(n-1)`. Since
`Q = ⟨S, t⟩`, choose `w_i ∈ S * ⟨x_1⟩` with `w_i(t) = g_i`, where `w_i(t)` is the image
of `w_i` under `x_1 ↦ t`. The map `α_g : x_i ↦ x_i w_i(x_1)` for `2 ≤ i ≤ n`, fixing `S`
and `x_1`, is an automorphism with inverse `x_i ↦ x_i w_i(x_1)^(-1)`. Then
`φ_0 ∘ α_g = (t, g_2, ..., g_n) =: ψ_g`, so every `ψ_g` lies in `O`.

**Step 2 (displacements vanish).** Suppose `β ∈ A` fixes every point of `O`. Put
`u_i = x_i^(-1) β(x_i) ∈ G`. For `ψ ∈ O`, `ψ(β(x_i)) = ψ(x_i)` gives `ψ(u_i) = 1`; in
particular `ψ_g(u_i) = 1` for every `g ∈ Q^(n-1)`.

**Step 3 (substitution is an isomorphism).** Define
`θ : G → Q * F(y_2, ..., y_n)` by `θ|_S = id`, `θ(x_1) = t`, `θ(x_i) = y_i` for
`i ≥ 2`. It renames the free generators of `S * ⟨x_1⟩ * ⟨x_2, ..., x_n⟩`, so it is an
isomorphism. Let `e_g : Q * F(y) → Q` be the identity on `Q` with `y_i ↦ g_i`. Then
`e_g ∘ θ = ψ_g`.

**Step 4.** By Steps 2 and 3, `θ(u_i)` is a word in `Q * F(y_2, ..., y_n)`, in `n - 1 ≥ 1`
variables, with `e_g(θ(u_i)) = 1` for every `g`. By MIF, `θ(u_i) = 1`, so `u_i = 1` and
`β(x_i) = x_i` for all `i`. Since `β` also fixes `S`, `β = id`. This proves item 1.

The variant with base point `(y_1, ..., y_k, 1, ..., 1)` into `S * F(y_1, ..., y_k)` is the
same argument. Substitute `x_i ↦ y_i` for `i ≤ k`, apply MIF of `S * F_k` in `n - k ≥ 1`
variables, and use the transvections `x_i ↦ x_i w_i(x_1, ..., x_k)` for `i > k` in Step 1.

**Item 2.** A permutation of `S^n ⊔ O` fixing every point fixes every point of `O`, so
item 1 applies. And `core_A(Stab_A(φ_0)) = ker(A ↷ O) = 1`.

**Item 3.** `ψ_j = φ_0 ∘ (x_2 ↦ x_2 x_1^j)` lies in `O`. The pair `(φ_0, ψ_j)` defines
`π_j : G → Q × Q`, `g ↦ (φ_0(g), ψ_j(g))`. Its image is `P_j = ⟨ΔS, (t, t), (1, t^j)⟩`.
- **Form of `P_j`.** `⟨ΔS, (t,t)⟩ = ΔQ`, and `ΔQ` normalizes `1 × ⟨⟨t^j⟩⟩`. So
  `P_j = ΔQ · (1 × ⟨⟨t^j⟩⟩)`, and `P_j ∩ (1 × Q) = 1 × ⟨⟨t^j⟩⟩`. By symmetry,
  `P_j ∩ (Q × 1) = ⟨⟨t^j⟩⟩ × 1`.
- **Invariance.** Precomposition by `α ∈ A` leaves the image of `π_j` unchanged, and
  swapping the pair swaps the factors. So the normal closure `⟨⟨t^j⟩⟩` is an invariant of
  the `A`-orbit of the unordered pair `{φ_0, ψ_j}`.
- **Distinctness.** `Q/⟨⟨t^j⟩⟩ ≅ S * Z/j`, in which `t` has order exactly `j`. So
  `t^i ∈ ⟨⟨t^j⟩⟩` iff `j` divides `i`, and the normal closures are pairwise distinct.

Hence the pairs `{φ_0, ψ_j}` lie in infinitely many orbits, and `H\A/H` is infinite.

**Calibration.** With target `S` instead of `Q` (BFFHZ Theorem E), Step 3 fails: `x_1 ↦ 1`
has kernel `⟨⟨x_1⟩⟩`. The surviving displacements are exactly the words of `J_n(S)`,
which is the kernel `K`. With target `Q`, Step 3 is an isomorphism, so nothing
survives. Item 3 is the price: all of `Q`'s normal subgroups show up as pair invariants.
