---
rg: 2
id: ghb7-contains-a-genus-two-surface-subgroup-proof
kind: route
title: A computer-certified labelled girth surface with 24 chambers gives a genus-two surface subgroup of GHB_2(7)
target: ghb7-contains-a-genus-two-surface-subgroup
requires: [ghb7-girth-surfaces-give-surface-subgroups, cckw-ghb2-kms-group-structure]
artifacts:
  - experiments/ghb7-girth-surfaces/certificates-genus2.json
  - experiments/ghb7-girth-surfaces/verify_certificate.py
  - experiments/ghb7-girth-surfaces/verify-genus2.log
  - experiments/ghb7-girth-surfaces/ghb7_girth_surfaces.py
  - experiments/ghb7-girth-surfaces/search-t24.log
  - research/artifacts/ideas-growth-hyperbolic-2026-09-14.md
---

## The certificate

`experiments/ghb7-girth-surfaces/certificates-genus2.json` lists six girth surfaces of size
`T = 24`, the orientable surfaces 25, 29, 31, 43, 65 and 67 of the enumeration. Each entry gives
`r_0, r_1, r_2` as lists and one label `[k, t, s, x]` for every side, where `t < s = r_k(t)`.
- Crossing from `t` to `s` multiplies by `g_k^x`; crossing back multiplies by `g_k^{−x}`.
- These are exactly the data of a girth surface in `ghb7-girth-surfaces-give-surface-subgroups`.

## Verification

`verify_certificate.py` shares no code with the search. Run on MSI, it checks every certificate
(`verify-genus2.log`, all PASS):
1. each `r_k` is a fixed-point-free involution, and `<r_0,r_1,r_2>` is transitive;
2. every orbit of `<r_1,r_2>`, `<r_0,r_2>`, `<r_0,r_1>` has exactly 6, 8, 8 distinct points;
3. the surface is orientable, with `V − E + F = 10 − 36 + 24 = −2`;
4. every one of the 36 sides carries a label in `1..6`;
5. for every chamber and every vertex type, the vertex word evaluates to the identity of
   `SL_4(F_7)` under `a ↦ I + E_03 + E_12`, `b ↦ I + E_10 − E_23`, `c ↦ I + E_31`;
6. these three matrices satisfy the eleven relators of `G`, with left-normed commutators
   `[x,y] = x^{-1}y^{-1}xy`, so they define `ψ`.

The search program also re-evaluated every solution it found by raw matrix products
(`search-t24.log`, `verified True`).

## Deduction

Each vertex word is a product of powers of the two edge generators at that vertex, so it lies in
`X_i`. `ψ` is injective on `X_i` (item 5 of `cckw-ghb2-kms-group-structure`; compiled as
`injective_psi_comp_u3ToAB`, `injective_psi_comp_u4ToCB`, `injective_psi_comp_u4ToCA`). So check 5
gives the vertex condition in `G`.

`ghb7-girth-surfaces-give-surface-subgroups` then gives an injective homomorphism
`π_1(S) → G` with quasiconvex image. Here `S` is orientable with `χ(S) = −24/12 = −2`, so it is
the closed orientable surface of genus 2.
