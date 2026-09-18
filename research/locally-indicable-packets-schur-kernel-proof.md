---
rg: 2
id: locally-indicable-packets-schur-kernel-proof
kind: route
title: Extend every Q/Z multiplier over the one-relator product by Howie's restriction epimorphism, then push forward and localize
target: locally-indicable-packets-have-zero-schur-kernel
requires: [howie-one-relator-product-h2-restriction-is-onto, howie-locally-indicable-nonsingular-equations-are-solvable, schur-kernel-localizes-to-coefficient-subgroup]
artifacts:
  - research/artifacts/sp4-schur-li-packets-2026-09-17.md
---

Sections 2 and 3 of the artifact.

**(1) `Q` locally indicable.** Conjugating `w` does not change `<<w>>`.

- *`w` conjugate into a factor.* Then `w ~ t^m` with `m != 0`, since the degree
  is nonzero. Here `G = Q * Z/m`, and `t -> 1` retracts `G` onto `Q`.
- *Otherwise.* Among the conjugates `R^n` of `w` with `R` cyclically reduced,
  choose `n` maximal. This is possible because a cyclically reduced `R` of
  length `l >= 2` has `R^n` cyclically reduced of length `n l`. By maximality,
  `R` is not a proper power.
  - `howie-one-relator-product-h2-restriction-is-onto` applies with factors `Q`
    and `<t>`, `k = 2` and `M = Q/Z`. So `H^2(G; Q/Z) -> H^2(Q; Q/Z)` is onto.
  - `Q/Z` is divisible, so `H^2(-; Q/Z) = Hom(H_2(-), Q/Z)` naturally. Every
    `gamma : H_2(Q) -> Q/Z` therefore factors through `H_2(G)`.
  - `Q/Z` is an injective cogenerator, so no nonzero class dies.

**(2) Images.** `phi * id` induces a map
`(Q * <t>)/<<w>> -> (L * <t>)/<<phi(w)>>`, and `phi(w)` has the same degree.
Naturality sends `K_2(Q, w)` into `K_2(L, phi(w))`, which is `0` by (1).

**(3) Packets.**

- `howie-locally-indicable-nonsingular-equations-are-solvable` makes `B` inject
  into `(B * <t>)/<<w>>`.
- `schur-kernel-localizes-to-coefficient-subgroup` then gives
  `K_2(Q, w) = iota_* K_2(B, w)`.
- Apply (1) and (2) to `B`.

**(4) p-local form.** Let `P = B/A`.

- By the injectivity hypothesis and
  `schur-kernel-localizes-to-coefficient-subgroup`,
  `K_2(Q, w) = iota_* K_2(B, w)`.
- By (2), `K_2(B, w) <= ker(H_2 B -> H_2 P)`.
- `|A|` is invertible in `Z_(p)`, so transfer gives `H_q(A; Z_(p)) = 0` for
  `q >= 1`.
- The Lyndon--Hochschild--Serre spectral sequence then gives
  `H_2(B; Z_(p)) = H_2(P; Z_(p))`.
- `Z_(p)` is flat, so `H_2(-; Z_(p)) = H_2(-) (x) Z_(p)`. Localization is
  exact, so the kernel tensored with `Z_(p)` is 0. Hence each element of the
  kernel has order prime to `p`.
- `iota_*` preserves this property, and a `Z/p`-valued homomorphism kills
  such elements.
