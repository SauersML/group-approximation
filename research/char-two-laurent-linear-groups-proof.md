---
rg: 2
id: char-two-laurent-linear-groups-proof
kind: route
title: Realize free and Laurent algebras by prefix monomials and a Thompson unit, then amplify the field
target: char-two-laurent-linear-groups-satisfy-boone-higman
requires:
  - leavitt-subalgebra-linear-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

Let `R = L_(F_2)(1,2)` with the notation of
`leavitt-subalgebra-linear-groups-proof`.

**A test module.** Let `M` be the `F_2`-vector space with basis `Omega`, the
binary sequences with finitely many ones. Put `s_a(w) = aw`, `t_a(aw) = w` and
`t_a(bw) = 0` for `b != a`. Then `t_a s_b = delta_ab`, and
`s_0 t_0 + s_1 t_1 = 1` because every `w` has a first letter. So `M` is a
unital `R`-module. A polynomial expression in `R` whose action on `M` is
nonzero is nonzero in `R`; no faithfulness of `M` is needed.

**Free algebras.** Let `rho_i = 1^(i-1)0` for `i = 1..m`, a prefix code. Send
`x_i |-> s_(rho_i)`. A monomial goes to `s_w`, where `w` is the concatenation
of the `rho`'s, and distinct monomials give distinct words. Apply to
`v = 1 0 0 0 ...`: `s_w(v) = w 1 0 0 ...` recovers `w` as the prefix before
the last one, so a nonzero `F_2`-combination of monomials sends `v` to a
nonzero vector. Hence `F_2<x_1..x_m> -> R` is injective.

**Laurent polynomials.** Put

```text
g = s_0 t_0 t_0 + s_1 s_0 t_1 t_0 + s_1 s_1 t_1,
h = s_0 s_0 t_0 + s_0 s_1 t_0 t_1 + s_1 t_1 t_1.
```

Expanding with `t_a s_b = delta_ab` leaves three surviving terms in each
product:
`gh = s_0 t_0 + s_1 (s_0 t_0 + s_1 t_1) t_1 = 1` and
`hg = s_0 (s_0 t_0 + s_1 t_1) t_0 + s_1 t_1 = 1`. So `g` is a unit, the
Thompson element with prefix replacements `00->0, 01->10, 1->11`. On `M`,
`g^k(v) = 1^(k+1) 0 0 ...` for `k >= 0` and `g^(-k)(v) = 0^k 1 0 0 ...` for
`k >= 1`. These are pairwise distinct basis vectors, so `t |-> g` gives an
injective unital map `F_2[t,t^-1] -> R`.

**Finite fields.** `F_q = F_2[c]/(p(c))` embeds unitally in `M_k(F_2)` by the
companion matrix, so `F_q ⊗ B` embeds in `M_k(B)` for `B = F_2[t,t^-1]` and
for `B = F_2<x_1..x_m>`. Blocks give unital injections
`M_n(F_q ⊗ B) -> M_(nk)(B)`, hence `GL_n(F_q[t,t^-1]) -> GL_(nk)(A)` and
`GL_n(F_q<x..>) -> GL_(nk)(A')`, with `A, A'` the images of `B` in `R`.

**Conclusion.** `leavitt-subalgebra-linear-groups-satisfy-boone-higman`
embeds `GL_(nk)(A)` and `GL_(nk)(A')` in `R^x`. `∎`
