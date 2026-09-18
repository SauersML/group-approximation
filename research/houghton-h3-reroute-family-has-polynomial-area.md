---
rg: 2
id: houghton-h3-reroute-family-has-polynomial-area
kind: claim
title: "In H_3 the reroute family R_3(k) = Area(D^u_x(k) D^v_x(k)^(-1)) is at most 2A(k) + |N_k| + 4k + 2, hence polynomial"
artifacts:
  - research/artifacts/zp-houghton-h3-families-via-reroute-2026-09-18.md
  - experiments/houghton-h3-families-2026-09-17/verify_h3_families.py
  - experiments/houghton-h3-families-2026-09-17/verify_h3_families.out
distinct_from:
  houghton-h3-five-three-ray-families-have-polynomial-area: that bounds all five families F_3, R_3, B_3, C_3, D_3; this bounds only the reroute family R_3, which the other four reduce to.
  houghton-three-ray-pours-have-polynomial-two-ray-normal-forms: that bounds the pour-versus-normal-form relation A(k); this uses it to bound the different relation D^u_x(k) D^v_x(k)^(-1).
  houghton-group-h3-has-polynomial-dehn-function: that bounds every null-homotopic word of H_3; this bounds one explicit linear-length family.
---

In `H_3`, with the presentation `P` of `research/artifacts/zp-houghton-pours-2026-09-17.md`
§0 and `D^u_x(k) = λ_xu^k τ_x λ_ux^k`, take `{x,u,v} = {1,2,3}` and `k >= 1`. Let `N_k`
and `A(k)` be the two-ray word and the area of Proposition 5 of
`research/artifacts/zp-houghton-pour-doubling-2026-09-18.md`, for the labeling
`(a,b,c) = (u,v,x)`. Then

```text
Area( D^u_x(k) · D^v_x(k)^(-1) ) <= 2 A(k) + |N_k| + 4k + 2,
```

and so `R_3(k) <= 8 (1 + log_2 k) k^(5 + log_2 K) + k^5 + 4k + 2`.

The proof is Lemma 1 of the artifact.

- Convert the inverse letters. The middle factor becomes the literal pour
  `λ_ux^k λ_xv^k`.
- Replace that pour by `N_k`, and move `τ_x` across `N_k` one letter at a time. This
  works because the letters of `N_k` miss ray `x`.
- Cancel `τ_x^2`, restore the pour, and cancel `2k` pairs.
