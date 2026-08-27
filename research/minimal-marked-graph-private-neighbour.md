---
rg: 2
id: minimal-marked-graph-private-neighbour
kind: claim
title: Every finite vertex set of the minimal marked orbital graph has a private neighbour
distinct_from:
  marked-double-coset-infinite-degree: that is an index computation — the degree of the marked orbital graph is infinite at every vertex — and says nothing about how neighbourhoods of different vertices overlap; this is a separation property of finite vertex SETS, which infinite degree neither gives nor is given by.
  invariant-graph-clifford-phase: that classifies the invariant-graph family and proves nondegeneracy equivalent to factoriality of the lamp algebra; this supplies the combinatorial input that decides which side of that equivalence the minimal member falls on.
  two-point-orbit-approximation: that is an approximation property of the G-set, quantified over finite models and Hamming-approximate homomorphisms; this is an exact statement inside the real graph on G/Gamma with no finite model, no epsilon and no deleted set in it.
  invariant-graph-crossed-product-ce: that is an analytic claim about Connes embeddability of a crossed product; this is finite combinatorics in the base G-set, and its role is to remove the existential over graphs from that claim's algebraic half.
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
  - notes/COMMUTING_WREATH_SOFIC_RADICAL.md
---

Let `q` be a prime power, `r,d ≥ 3`, `R₊ = F_q[x₁,…,x_d]`,
`R = F_q[x₁^{±1},…,x_d^{±1}]`, `Γ = EL_r(R₊)`, `N = EL_r(R)`,
`G = N ⋊ SL_d(ℤ)` the Kun--Thom Theorem E pair, `X = G/Γ`, and

```text
m = x₁⋯x_d,   μ = m^{-1},   h = e₁₂(μ),   D = ΓhΓ
```

the marked element and its double coset.  Let `S_min` be the orbital graph of
`D` — the smallest `G`-invariant graph on `X` containing the marked edge
`{Γ, hΓ}`.

**Claim.**  For every nonempty finite `F ⊆ X` there is a vertex `z ∈ X` with

```text
|N_{S_min}(z) ∩ F| = 1.
```

Two components of the proof are separately reusable and are asserted here as
part of the claim.

1. **Symmetry and root transitivity.**  For `r ≥ 3` and every characteristic,
   `ΓhΓ = Γh^{-1}Γ`, and `h_{pq} = e_{pq}(μ) ∈ D` for every `p ≠ q`.  So
   `S_min` is a graph and marked neighbours are available in every root
   direction.
2. **Explicit neighbour chart.**  For fixed `p ≠ q` the map
   `a ↦ z_a = e_{qp}(a)h_{pq}Γ` sends `R₊` into the neighbourhood of the base
   point and satisfies `z_a = z_b ⟺ a − b ∈ m²R₊`, giving an injection

   ```text
   R₊ / m²R₊  ↪  N_{S_min}(Γ).
   ```

   The exact stabilizer computation behind it is
   `U_{qp} ∩ Γ ∩ h_{pq}Γh_{pq}^{-1} = { e_{qp}(a) : a ∈ m²R₊ }`.

The mechanism is that a coset `gΓ ≠ Γ` in the component `N/Γ` must carry a
Laurent denominator (Suslin stability), that a single polynomial row shear in
`Γ` can move the denominators of any finite competitor family into one common
row, and that adjacency of `z_a` to a competitor then confines `a` to one
coset of a denominator ideal, which has infinite additive index.  Finitely
many such cosets do not cover `R₊`.

Full proof, with the general-characteristic matrix arithmetic and the checks:
`research/artifacts/kun-thom-private-neighbour-2026-08-18.md`.

## Scope

The statement is about the specific Laurent pair and the specific marked
element `e₁₂((x₁⋯x_d)^{-1})`.  It is a statement about the `G`-set only: no
lamp, no algebra and no approximation notion occurs in it.  It does not
assert anything about larger invariant graphs — those contain `S_min` and
their radicals are separately, and more easily, zero — and nothing about
Connes embeddability.
