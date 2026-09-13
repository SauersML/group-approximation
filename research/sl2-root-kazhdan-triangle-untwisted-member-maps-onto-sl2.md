---
rg: 2
id: sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2
kind: claim
title: The untwisted Kazhdan SL_2 root triangle maps onto SL_2(q^2) injectively on its vertex groups, so it is virtually torsion-free
distinct_from:
  kazhdan-hyperbolic-sl2-root-triangles: that proves hyperbolicity and property (T) for every gluing; this exhibits one gluing with a vertex-injective finite quotient, the calibration member of that family
---

Take the data of `kazhdan-hyperbolic-sl2-root-triangles` with `q = 2^f >= 4`, `k = F_q ⊂ F = F_{q^2}`,
`s ∈ F \ k`. Use the parametrized embeddings with every gluing automorphism the identity:
- `A_1`: `E_12 ∋ x ↦ u(x)` and `E_13 ∋ x ↦ v(x)`;
- `A_2`: `E_12 ∋ x ↦ u(x)` and `E_23 ∋ x ↦ v(x)`;
- `A_3`: `E_13 ∋ x ↦ u(x)` and `E_23 ∋ x ↦ v(sx)`.

Call the colimit `Λ_0`.

**ESTABLISHED.** Let `P = s^{-1/2} ∈ F`, which exists because squaring is bijective in characteristic 2,
and put

```text
h = [[P, 1], [1, 0]],        h' = h·u(1/P) = [[P, 0], [1, 1/P]]     (both in SL_2(F)).
```

Then `ρ_1 = conj_h` on `A_1`, `ρ_2 = conj_{h'}` on `A_2`, and `ρ_3 = id` on `A_3` agree on the three edge
groups. So they define a homomorphism `ρ: Λ_0 -> SL_2(F)`, injective on every vertex group and onto,
since `ρ_3` already is.
- By `triangle-of-groups-half-girth-structure` (iv), `ker ρ` is torsion-free of index `|SL_2(q^2)|`.
- So `Λ_0` is virtually torsion-free and has a nontrivial finite quotient; for `q >= 8` it is moreover
  hyperbolic and Kazhdan. It is **not** a candidate for
  `hyperbolic-simple-triangle-group-without-finite-quotients`.

**Other gluings.** Twisting `E_23` by `x ↦ λx` with `λ ∈ k^*` is absorbed by `P = (λ/s)^{1/2}`. Candidates
must use gluings that no such configuration absorbs; see
`sl2-root-kazhdan-triangle-without-finite-quotients`.

Proof: `sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2-proof`.
