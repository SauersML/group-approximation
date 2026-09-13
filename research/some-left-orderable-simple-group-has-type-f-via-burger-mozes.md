---
rg: 2
id: some-left-orderable-simple-group-has-type-f-via-burger-mozes
kind: route
title: A left-orderable torsion-free simple cocompact lattice in a product of two trees is a left-orderable simple group of type F
target: some-left-orderable-simple-group-has-type-f
requires:
  - some-simple-lattice-in-a-product-of-trees-is-left-orderable
---

Let `Γ ≤ Aut(T_1) × Aut(T_2)` be a torsion-free, simple, left-orderable cocompact lattice,
for locally finite trees `T_1`, `T_2`. It remains to show that `Γ` is of type F.

1. `X = T_1 × T_2` is a locally finite square complex, contractible as a product of
   trees. `Aut(T_1) × Aut(T_2)` acts on it by cellular automorphisms, with compact open
   cell stabilizers.
2. `Γ` is discrete, so the stabilizer in `Γ` of any cell is finite, hence trivial because
   `Γ` is torsion-free.
3. `Γ` acts freely on `X`, not only on cells. Suppose `g ∈ Γ` maps a cell to itself.
   Then `g` permutes the at most four vertices of that cell, so `g^(24)` fixes a vertex.
   So `g^(24) = 1` by step 2, and `g = 1` because `Γ` is torsion-free.
4. `Γ` is cocompact and `X` is locally finite, so `X/Γ` is a finite square complex. It is
   a `K(Γ,1)` because its universal cover `X` is contractible and `Γ` acts freely.
5. So `Γ` is of type F, simple and left-orderable. This is
   `some-left-orderable-simple-group-has-type-f`.
