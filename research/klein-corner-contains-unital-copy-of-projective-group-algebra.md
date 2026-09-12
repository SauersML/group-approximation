---
rg: 2
id: klein-corner-contains-unital-copy-of-projective-group-algebra
kind: claim
title: The Klein corner of the ternary projective group algebra contains a unital copy of the whole group algebra
distinct_from:
  projective-ternary-klein-idempotent-is-full: that asks for a partial isometry pair c e_K b = 1; this gives only a unital subring copy of F_3[PG] inside the corner e_K F_3[PG] e_K, which is weaker.
  leavitt-units-embed-in-their-scalar-quotient: that embeds the unit group into its scalar quotient by a corner map on one coordinate; this doubles a group element diagonally and embeds the group algebra into a corner cut by the Klein idempotent.
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
---

Let `k = F_3`, `R = L_k(1,2)`, `PG = R^x/{±1}`, `K = <wbar, dbar>` with `w = s_0 t_1 + s_1 t_0` and
`d = s_0 t_0 - s_1 t_1`, and `e_K = sum_(k in K) [k]`. Let `delta(g) = s_0 g t_0 + s_1 g t_1`, a group
endomorphism of `PG`, and `delta_*` its linear extension. Then `x -> delta_*(x) e_K` is an injective
unital ring homomorphism `k[PG] -> e_K k[PG] e_K`.

The doubled elements commute with `w` and `d`. The products `delta(g) k` are pairwise distinct,
because a doubled element is scalar-diagonal and only `±1` in `K` is. Proposition 7 of the artifact.
