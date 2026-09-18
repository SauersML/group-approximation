---
rg: 2
id: quantum-automaton-multiplication-injective-proof
kind: route
title: The local multiplication maps are isometric for the min norm, and their union is dense in the global tensor product
target: quantum-automaton-multiplication-map-is-injective-globally
requires: []
---

This is a self-contained proof (referee ref-04, 2026-09-17). It fills Step 4 of
`quantum-endomorphisms-split-off-their-relative-commutant-proof`. Write `B = Phi(A)`, `B_L = Phi(A_L)` for finite
`L`, and `D = B' n A`.

**Step 0 (local matrix slicing).** Let `P = M_k` be a unital full matrix subalgebra of a unital C*-algebra `A`, with
matrix units `f_ij`, and put `E = P' n A`. Multiplication `P (x) E -> A` is an injective *-homomorphism.
- It is a *-homomorphism because `P` and `E` commute.
- It is injective: if `sum_ij f_ij y_ij = 0` with `y_ij` in `E`, then for fixed `i, j`,
  `0 = sum_k f_ki (sum_ab f_ab y_ab) f_jk = sum_k sum_ab f_ki f_ab f_jk y_ab = sum_k f_kk y_ij = y_ij`.
- Since `P` is finite dimensional, `P (.) E = P (x)_min E`, so this is an injective *-homomorphism of C*-algebras,
  hence isometric.

**Step 1 (a global map exists).** `B` and `D` are commuting C*-subalgebras of `A`. By the universal property of the
maximal tensor product there is a *-homomorphism `m : B (x)_max D -> A` with `m(b (x) x) = b x`. `B` is isomorphic to
`A` (`Phi` is injective), a UHF algebra, hence nuclear, so `B (x)_max D = B (x)_min D`. Thus `m` is a contractive
*-homomorphism `B (x)_min D -> A`.

**Step 2 (isometric on each local piece).** Fix finite `L`. `B_L` is a unital copy of `M_(d^|L|)`, and
`D <= B_L' n A`. The min norm is spatial, so `B_L (x)_min D` sits isometrically inside `B (x)_min D`, and it sits
isometrically inside `B_L (x)_min (B_L' n A)`. On it, `m` agrees with the multiplication map of Step 0 for
`P = B_L`, which is isometric. So `m` is isometric on `B_L (x) D` for every finite `L`.

**Step 3 (density).** The finite sets `L` are directed, and `B_L <= B_L'` when `L <= L'`. The union of the `B_L` is
dense in `B`, because the union of the `A_L` is dense in `A` and `Phi` is isometric. Hence the union of the
`B_L (.) D` contains every elementary tensor `b (x) x` up to arbitrarily small min-norm error, and so it is dense in
`B (x)_min D`.

**Step 4 (conclusion).** `m` is contractive and isometric on a dense subspace, so `m` is isometric on
`B (x)_min D`. In particular it is injective, and its restriction to the algebraic tensor product `B (.) D` is
injective. Its range is closed, being the range of an isometry.

So multiplication `Phi(A) (.) D -> A` extends to an injective *-homomorphism `Phi(A) (x)_min D -> A`, which is the
target statement.
