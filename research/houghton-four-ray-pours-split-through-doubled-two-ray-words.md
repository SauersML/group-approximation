---
rg: 2
id: houghton-four-ray-pours-split-through-doubled-two-ray-words
kind: route
title: Split the four-ray skew square through the doubled two-ray word N_m, which represents both routes, and fill each half by the H_3 pour area
target: houghton-four-ray-pour-route-change-is-polynomial
requires:
  - houghton-three-ray-pours-have-polynomial-two-ray-normal-forms
  - houghton-groups-have-at-most-exponential-dehn-function
artifacts:
  - research/artifacts/zp-houghton-pour-doubling-2026-09-18.md
  - research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md
  - experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.py
---

The proof is Theorem 6 of `research/artifacts/zp-houghton-pour-doubling-2026-09-18.md`.

- **Same word on both sides.** Fix distinct rays `a,b,c,d`. The substitution table
  defining `N_m` involves only rays `a` and `b`. It is valid for both constructions,
  with `c` special (conjugating by `λ_ca`) and with `d` special (conjugating by
  `λ_da`). The swap of `c` and `d` is an automorphism of `H_4` fixing every two-ray
  letter. So one word `N_m` represents both `E^c_(a,b)(m)` and `E^d_(a,b)(m)`. Check (6)
  of the script confirms this in `H_4` for `m <= 40`.
- **Split.** `E^c (E^d)^(-1)` is freely equal to `(E^c N_m^(-1)) (E^d N_m^(-1))^(-1)`.
  The first factor has its letters in the stabilizer `S_d ≅ H_3` of ray `d`, and the
  second in `S_c ≅ H_3`.
- **Fill each half.** Use Lemma 2 of
  `research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md` (area transfer from
  a ray stabilizer, using only that `H_3` is finitely presented). Apply it to the one
  fixed diagram of `houghton-three-ray-pours-have-polynomial-two-ray-normal-forms`
  for the relevant labeling, instead of via `δ_(H_3)`. With `θ` and `ι` the identity on
  the letters `λ_yz, τ_y`, this gives `W_4(m) <= 2 K_1 max A(m)` over the 24
  labelings.
- **Result.** `W_4(m) ≼ m^β` for every `β > 5 + log_2 K_max`.

This is Remark 3.1 of the four-ray note ("the proof of Theorem 3 uses `δ_(H_3)` only on
one explicit family"), with the doubled word `N_m` in place of the bubble sort.
