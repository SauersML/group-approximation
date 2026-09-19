---
rg: 2
id: quasi-free-subfield-bound-via-koszul-ext
kind: route
title: Tensor the length-one bimodule resolution with a module for the upper bound, and induce the Koszul resolution of the diagonal from a subfield for the lower bound
target: quasi-free-algebras-have-no-trdeg-two-subfields
requires: []
---

All tensor products are over `k` unless marked. Modules are left modules.

## 1. Upper bound

Fix a resolution of `A`-bimodules `0 -> P_1 -> P_0 -> A -> 0` with `P_0, P_1` projective over `A^e`.
Let `U` be semisimple and `M` an `A ⊗ U`-module, that is, an `A`-module with a commuting `U`-action.

- **Exactness.** `A` is free as a right `A`-module, so the sequence splits as right `A`-modules. Hence
  `0 -> P_1 ⊗_A M -> P_0 ⊗_A M -> M -> 0` is exact.
- **Module structure.** Each term is an `A ⊗ U`-module: `A` acts through the left bimodule action of `P_i`, and `U`
  acts on the factor `M`. The maps are `A ⊗ U`-linear, and `A ⊗_A M = M` with its given structure.
- **Projectivity.** For `P = A^e` we get `A^e ⊗_A M ≅ A ⊗ M ≅ (A ⊗ U) ⊗_U M`. This is projective over `A ⊗ U`,
  because `M` is projective over the semisimple `U`. Direct sums and summands follow, so each `P_i ⊗_A M` is
  projective.

So `pd_(A⊗U) M <= 1` for every `M`, and `l.gl.dim(A ⊗ U) <= 1`. A division ring is semisimple, which covers
`U = A^op` when `A` is a division ring.

## 2. Lower bound

Let `F ⊆ A'` with `1_(A') ∈ F`, and fix an isomorphism `φ : K -> F` with `K = k(y_1, ..., y_n)`.

**The subring.** Put `S = F ⊗ K ⊆ R = A' ⊗ K`. It is injective because `k` is a field.
- `A'` is a left and a right `F`-vector space. Choosing bases, `R` is free as a left and as a right `S`-module, on
  a nonempty basis.
- Via `φ`, `S ≅ k(y) ⊗ k(y')`. This is the localization of `k[y, y'] = k[y_1, ..., y_n, y'_1, ..., y'_n]` at
  `T = {f(y) g(y') : f, g ≠ 0}`. So `S` is commutative and noetherian.

**The diagonal.** Let `z_i = y_i - y'_i` and `I = (z_1, ..., z_n) ⊆ S`.
- In `k[y', z] = k[y, y']` the `z_i` are variables, so they form a regular sequence.
- `T^(-1)` is flat, so the sequence stays regular in `S`.
- `S / I = T^(-1) k[y']`, where `f(y) g(y')` maps to `f(y') g(y') ≠ 0`. So `L := S / I ≅ k(y') ≠ 0`.
- The Koszul complex `K_•` is a finite free resolution of `L` of length `n`.
- It is self-dual, so `Ext^n_S(L, S) ≅ S / I = L ≠ 0`.

**Induction.** Put `Q = R ⊗_S L`.
- `R` is right `S`-free, so `R ⊗_S K_•` is a free `R`-resolution of `Q`.
- Adjunction gives `Hom_R(R ⊗_S K_j, R) ≅ Hom_S(K_j, R)`, with `R ≅ ⊕_J S` as left `S`-modules.
- Each `K_j` is finite free, so this is `⊕_J Hom_S(K_j, S)`, naturally in `j`.
- Hence `Ext^n_R(Q, R) ≅ ⊕_J Ext^n_S(L, S) ≅ ⊕_J L ≠ 0`.

So `pd_R Q >= n`, and `l.gl.dim(A' ⊗ K) >= n`. ∎

## 3. Consequence

Suppose `F ⊆ M_r(A)` is a commutative subfield with `k · 1 ⊆ F` and `trdeg_k F >= 2`.
- Choose `a, b ∈ F` algebraically independent over `k`. The subfield they generate is `F_0 ≅ K = k(y_1, y_2)`,
  and it contains `1`.
- By §2 with `A' = M_r(A)`, `l.gl.dim(M_r(A) ⊗ K) >= 2`.
- But `M_r(A) ⊗ K ≅ M_r(A ⊗ K)` is Morita equivalent to `A ⊗ K`. Global dimension is Morita invariant, so by §1
  this is `<= 1`.

This is a contradiction. The "in particular" form holds because, for commuting independent `a, b` with every
`p(a, b) ≠ 0` invertible, the elements `p(a, b) q(a, b)^(-1)` form such a subfield. ∎

**Provenance.** §1 is the standard estimate `gl.dim(A ⊗ B) <= pd_(A^e) A + gl.dim B`, specialized to semisimple
`B`. For division rings it is Schofield, *Stratiform simple Artinian rings*, Proc. LMS 53 (1986), Lemma 2, p. 269.
It is proved in full above, so no import is used.
