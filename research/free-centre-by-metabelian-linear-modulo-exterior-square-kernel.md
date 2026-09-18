---
rg: 2
id: free-centre-by-metabelian-linear-modulo-exterior-square-kernel
kind: claim
title: For every rank n, n^2 explicit 3x3 representations over Z[Z^n] embed F_n/[F_n'',F_n] modulo one explicit kernel K_n; if K_3 = 0 then the rank-3 group is linear
distinct_from:
  free-centre-by-metabelian-group-of-rank-two-is-linear: that proves rank 2 outright (there K_2 = 0, shown directly); this is the rank-n construction and isolates exactly what is missing in rank >= 3.
  free-centre-by-metabelian-groups-linear-iff-residually-finite: that reduces linearity for n >= 4 to residual finiteness, using Gupta 1973; this gives an explicit representation whose kernel is a named subgroup, with no citation.
---

**ESTABLISHED** (lane proof, elementary, inline below; not independently reviewed; no
novelty claimed, since C. K. Gupta (1969, 1973) works with 3x3 representations of this
family and this is probably a form of his construction).

## Statement

Let `F = F(x_1, …, x_n)`, `G = F/F' = Z^n`, `R = Z[G] = Z[x_i^(±1)]`. Let
`b: F'/F'' -> R^n` be the Magnus map, `b(u)_j` = the image of `∂u/∂x_j` (injective by
Magnus). Define

```text
K_n := ker( F''/[F'', F]  ->  (Λ²_Z R^n)_G ),     [u, v] ↦ b(u) ∧ b(v),
```

where `(·)_G` denotes coinvariants for the diagonal action of the monomials. Then:
1. `C_n/K_n` embeds in `GL_(3n^2)(R) ⊂ GL_(3n^2)(Q(x_1, …, x_n))`, and is therefore
   linear in characteristic zero. If `K_n = 0`, then `C_n` is linear and lies in `B_A`.
2. `K_2 = 0` (`free-centre-by-metabelian-rank-two-linearity-proof`, Step 4).
3. `(Λ²_Z R^n)_G` is free abelian, so `K_n` contains the torsion of `F''/[F'', F]`. By
   Gupta 1973 (abstract), `K_n ≠ 0` for `n >= 4`.
4. **Open:** whether `K_3 = 0`. A yes gives `C_3` linear, hence in `B_A`.

## Construction

For `j, k ∈ {1..n}`, let `rho_(jk)` send `x_i` to the 3x3 matrix
`N(δ_ij, x_i, δ_ik, 0)`, where `N(α, g, β, γ) = [[1, α, γ], [0, g, β], [0, 0, 1]]`.
The group law is
`N(α,g,β,γ) N(α',g',β',γ') = N(α' + α g', g g', β + g β', γ + γ' + α β')`.
Take `rho = ⊕_(j,k) rho_(jk)`, block-diagonally in `GL_(3n^2)(R)`.

## Proof

1. In `rho_(jk)(w)`, the entries are as follows:
   - the middle entry is `g(w)`;
   - the right entry is `b_k(w)`;
   - the top entry is `α_j(w)`, where `α_j(uv) = α_j(v) + α_j(u) g(v)` and
     `α_j(x_i) = δ_ij`;
   - the corner is `γ_(jk)(w)`.
2. **The top entry in terms of Fox derivatives.** Put `b̃_j(w) := \overline{b_j(w^(-1))}`,
   where `\overline{·}` is the involution of `R` inverting monomials. It satisfies the
   same recursion as `α_j`, and `b̃_j(x_i) = −x_i δ_ij`. So `α_j = −x_j^(-1) b̃_j`. For
   `u ∈ F'` we have `b(u^(-1)) = −b(u)`, hence `α_j(u) = x_j^(-1) \overline{b_j(u)}`.
3. **Kernel lies in F''.** On `F'` all of `α_j`, `b_k` are additive and conjugation-covariant.
   So `rho(F'')` lies in the central subgroup of corner matrices, and `rho([F'', F]) = 1`.
   If `rho(w) = 1`, then `g(w) = 1` and `b(w) = 0`, so `w ∈ F''` by Magnus.
4. **Corners.** For `u, v ∈ F'`, as in the rank-2 proof,
   `γ_(jk)([u,v]) = α_j(u) b_k(v) − α_j(v) b_k(u)`. With `β = b(u)`, `β' = b(v)`, the
   `(j, k)` corner is `x_j^(-1) ( \overline{β_j} β'_k − \overline{β'_j} β_k )`.
   So on `F''/[F'', F]` the joint corner map is `Φ ∘ (b ∧ b)`, where `Φ: (Λ²_Z R^n)_G -> R^(n×n)`
   is `β ∧ β' ↦ ( x_j^(-1)(\overline{β_j} β'_k − \overline{β'_j} β_k) )_(j,k)`.
5. **Φ is injective.** A Z-basis of `(Λ²_Z R^n)_G` consists of the orbit classes of
   `f_i ∧ h f_(i')`:
   - `i < i'` with `h ∈ G` arbitrary;
   - `i = i'` with `h ≠ 1`, taken up to `h ↔ h^(-1)`.

   There are no sign collapses, because `G` is torsion-free. These classes map to
   `x_i^(-1) h E_(ii') − x_(i')^(-1) h^(-1) E_(i'i)`, respectively
   `x_i^(-1)(h − h^(-1)) E_(ii)`. Their supports (matrix position, monomial) are pairwise
   disjoint, so the images are Z-linearly independent.
6. So `ker rho = ` the preimage of `K_n` in `F`, which proves 1. Part 3 holds because
   `(Λ²_Z R^n)_G` is free abelian. ∎

## Where the rank-3 question sits

`F'/F'' ≅ M := ker(R^3 -> R, r ↦ Σ r_j (x_j − 1))`, which is `R^3` modulo the Koszul
vector. `M` is pure in `R^3` (the quotient is the augmentation ideal, torsion-free), so
`Λ²_Z M -> Λ²_Z R^3` is injective. Only the coinvariant step can create kernel:
`K_3` is the image in `F''/[F'', F]` of `ker((Λ²_Z M)_G -> (Λ²_Z R^3)_G)`.
