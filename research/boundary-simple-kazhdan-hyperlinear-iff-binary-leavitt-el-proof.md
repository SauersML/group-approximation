---
rg: 2
id: boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el-proof
kind: route
title: Sandwich EL_N(L_p) inside a corner of S_∂ and S_∂ as a finite central quotient of a subgroup of EL_M(L_p)
target: boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el
requires:
  - boundary-crossed-product-embeds-unitally-in-binary-leavitt
  - boundary-crossed-product-carries-leavitt-family
  - leavitt-algebras-l-k-1-n-are-simple
  - steinberg-elementary-groups-are-simple-mod-centre
artifacts:
  - research/artifacts/sk-hyperlinear-boundary-a-reduction-2026-09-13.md
---

Notation: `R = LC(∂F_d, k) ⋊ F_d`, `m = [k : F_p]`, `L_p = L_(F_p)(1,2)`. Full details are in §2 of the artifact.

**(i) Rank independence.** For any ring `S`, `M >= 2` and `n >= 1`, `E_M(M_n(S)) = E_(Mn)(S)` inside `GL_(Mn)(S)`.
- `I + X E_(ij)`, with `X` in `M_n(S)` and `i != j`, is a product of commuting elementary matrices.
- `e_((i,a),(i,b))(x) = [e_((i,a),(j,c))(x), e_((j,c),(i,b))(1)]` for `j != i`.

Since `L_p ≅ L_p^2` as modules, `M_2(L_p) ≅ L_p`. So `EL_M(L_p) ≅ EL_(2M)(L_p)`, and together with
`EL_M ≤ EL_(M+1) ≤ EL_(2M)` all of these groups embed in one another.

**(ii ⇐).** `R ↪ L_k(1,2)` unitally (`boundary-crossed-product-embeds-unitally-in-binary-leavitt`).
`L_k(1,2) ≅ k ⊗_(F_p) L_p ↪ M_m(F_p) ⊗ L_p = M_m(L_p)` unitally, using the regular representation of `k`. So by
(i), `EL_N(R) ≤ E_(Nm)(L_p)` is hyperlinear.

By `steinberg-elementary-groups-are-simple-mod-centre` the centre `Z` lies in `k^x I_N`, which is finite. A
quotient `G/F` by a finite normal subgroup `F` of a hyperlinear group is hyperlinear:
- `q = |F|^(-1) sum_(f in F) λ_f` is a central projection of trace `1/|F|` in `L(G)`, and `L(G/F) ≅ qL(G)` with the
  normalized trace;
- a corner of an `R^ω`-embeddable tracial algebra by a projection of positive trace is `R^ω`-embeddable, by lifting
  `q` to projections of normalized rank tending to `1/|F|`;
- hyperlinear is equivalent to `L(G) ⊂ R^ω`.

So `S_∂(d,k)` is hyperlinear.

**(iii).** Since `M_M(L_p) ≅ L_p`, `E_(Nm)(L_p) ≤ GL_(Nm)(L_p) ≅ L_p^x`. Then argue as in (ii ⇐).

**(ii ⇒).** Let `s_i`, `t_i` be the unital `d`-ary Leavitt family in `R` (`boundary-crossed-product-carries-leavitt-family`).
- **Corner copy.** Put `e = s_1 t_1`. The map `x ↦ s_1 x t_1` is a unital ring isomorphism `R ≅ eRe`, and
  `X ↦ X + (1-e) I_N` embeds `EL_N(eRe)` in `EL_N(R)`, meeting `k^x I_N` only in `I_N`. So `EL_N(R)` embeds in
  `S_∂(d,k)`, hence is hyperlinear.
- **Binary family in a corner.** Put `f = sum_(i<d) s_i t_i`. The `2d-2` words
  `w = s_1, ..., s_(d-2), s_(d-1)s_1, ..., s_(d-1)s_d`, with adjoints `t_1, ..., t_(d-2), t_1 t_(d-1), ..., t_d t_(d-1)`,
  satisfy `w_k^* w_(k') = delta_(kk')` and `sum_k w_k w_k^* = f`. For `j = 1,2` put
  `a_j = sum_(i=1)^(d-1) w_((j-1)(d-1)+i) t_i` and `b_j = sum_(i=1)^(d-1) s_i w_((j-1)(d-1)+i)^*`.
  Then `a_j, b_j` lie in `fRf`, `b_j a_(j') = delta_(jj') f` and `a_1 b_1 + a_2 b_2 = f`. So there is a unital
  homomorphism `L_p -> fRf`, injective by `leavitt-algebras-l-k-1-n-are-simple`.
- Then `EL_N(L_p) ≤ EL_N(fRf) ≤ EL_N(R)` through `X ↦ X + (1-f) I_N`, so `EL_N(L_p)` is hyperlinear, and by (i)
  so is `EL_3(L_p)`.
