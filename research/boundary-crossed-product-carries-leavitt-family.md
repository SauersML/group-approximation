---
rg: 2
id: boundary-crossed-product-carries-leavitt-family
kind: claim
title: The algebraic crossed product LC(∂F_d, k) ⋊ F_d carries an explicit unital d-ary Leavitt family, for every field k and d >= 2
distinct_from:
  purely-infinite-simple-algebras-have-nonsofic-el-groups: that proves nonsoficity for purely infinite simple algebras through Ara–Goodearl–Pardo; this writes down the Leavitt relations inside the boundary crossed product itself, with no pure infiniteness theory.
  boundary-action-elementary-simple-kazhdan-not-mf: that is the MF statement for the elementary groups of this ring from type-semigroup paradox; this is the exact ring-level family behind it.
---

Let `F_d = <c_1, ..., c_d>`, `d >= 2`, act on its boundary `∂F_d`, and let `R_∂ = LC(∂F_d, k) ⋊ F_d` over any field
`k`. With `P_U` the indicator of a clopen `U`, `C(w)` the cylinder of words beginning with `w`, and `u_g` the
canonical units, put

```text
s_i = P_(C(c_i)) + u_(c_i^(-1)) (1 - P_(C(c_i))),        t_i = P_(C(c_i)) + u_(c_i) P_(C(c_i^(-1))).
```

Then `t_i s_j = delta_ij` and `sum_i s_i t_i = 1`. So `R_∂ ≅ R_∂^d` as right modules, and there is a unital
homomorphism `L_k(1,d) -> R_∂`, which is injective by `leavitt-algebras-l-k-1-n-are-simple`.

ESTABLISHED by `boundary-crossed-product-carries-leavitt-family-proof` (unreviewed).
