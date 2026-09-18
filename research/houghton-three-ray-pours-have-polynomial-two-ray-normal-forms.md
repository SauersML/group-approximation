---
rg: 2
id: houghton-three-ray-pours-have-polynomial-two-ray-normal-forms
kind: claim
title: "In H_3 the pour λ_ac^m λ_cb^m rewrites with polynomial area into an explicit two-ray word N_m of length at most m^5"
artifacts:
  - research/artifacts/zp-houghton-pour-doubling-2026-09-18.md
  - experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.py
  - experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.out
distinct_from:
  houghton-four-ray-pour-route-change-bounded-by-h3-dehn: that bounds the four-ray route change by δ_(H_3) through the bubble-sort word λ_ab^m ρ_b(m) and leaves the H_3 area of the pour unbounded; this bounds the H_3 area of the pour against a different two-ray word unconditionally.
  houghton-h3-five-three-ray-families-have-polynomial-area: that is the five families B_3, C_3, D_3, F_3, R_3 equivalent to a polynomial Dehn function of H_3; this is the different family A_3 (pour against two-ray normal form), which is not one of the five and does not bound them.
---

Work in `H_3` with rays `a,b,c` and the finite presentation `P_3` of
`research/artifacts/zp-houghton-pours-2026-09-17.md` §0. There are two-ray words `N_m`
in the letters `λ_ab, λ_ba, τ_a, τ_b` and a constant `K >= 1` such that, for all
`m >= 1`:

- `N_m` represents `E^c_(a,b)(m) = λ_ac^m λ_cb^m`, and `|N_m| <= m^5`;
- `A(m) = Area_(P_3)( λ_ac^m λ_cb^m · N_m^(-1) ) <= 4 (1 + log_2 m) · m^(5 + log_2 K)`.

The words are given explicitly by `N_1 = λ_ab`, `N_(2m) = Δ̂(N_m)`,
`N_(2m+1) = ψ(N_(2m)) λ_ab`. Here `Δ̂` and `ψ` are letterwise substitutions of
length at most 8 and 3, listed in the table of §2 of the artifact.
