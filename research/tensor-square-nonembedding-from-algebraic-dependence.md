---
rg: 2
id: tensor-square-nonembedding-from-algebraic-dependence
kind: route
title: A unital map from the tensor square would produce two algebraically independent commuting units
target: no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2
requires: [leavitt-commuting-units-are-algebraically-dependent]
---

Let `L = L_(F_2)(1,2)` and suppose `f : L ⊗ L -> L` is a unital homomorphism.

1. `L` is simple (`leavitt-algebras-l-k-1-n-are-simple`) with center `F_2` (argument below). A tensor product
   over `F_2` of a central simple algebra with a simple algebra is simple. So `L ⊗ L` is simple, and `f` is
   injective.
2. Let `c = s_00 t_0 + s_01 t_10 + s_1 t_11`, of infinite order. Then `F_2[c^(+-1)]` is a Laurent polynomial ring.
   The inclusion `F_2[c^(+-1)] ⊗ F_2[c^(+-1)] -> L ⊗ L` is injective (tensor products over a field), and its
   source is the Laurent ring `F_2[x^(+-1), y^(+-1)]`.
3. So `a = f(c ⊗ 1)` and `b = f(1 ⊗ c)` are commuting units of `L`, and `P(a, b) = 0` forces `P = 0`. This
   contradicts `leavitt-commuting-units-are-algebraically-dependent`. ∎

**The center of `L` is `F_2`.** Let `z` be central.
- Grade `L` by the free group on `x_0, x_1` (`leavitt-free-group-leading-term-forces-linear-depth`). Every
  homogeneous component `z_g = s_μ f t_ν` commutes with the diagonal `D = span{ s_w t_w }`, since `D` is homogeneous
  of degree `1`. Here `f in D` is nonzero and `μ, ν` have no common last letter.
- Suppose `μ != ν`. The partial map `νy -> μy` has at most one fixed point. Choose `y` in the support of `f` with
  `μy != νy`, and a cylinder `[w]` containing `μy` but not `νy`. For functions supported near `νy`, the operator
  `z_g 1_[w]` gives `0` near `μy`, while `1_[w] z_g` does not. This contradicts commutation, so `z` lies in `D`.
- `z = 1_E` commutes with every Thompson unit `g`, so `E` is `g`-invariant for all `g in V`. `V` acts minimally
  on the Cantor set, so `E` is empty or everything, and `z` is in `F_2`. ∎
