---
rg: 2
id: houghton-three-ray-pours-by-route-ray-doubling
kind: route
title: Double the pour with the route ray as the special ray of the doubling endomorphism, and conjugate by λ_ca for odd sizes
target: houghton-three-ray-pours-have-polynomial-two-ray-normal-forms
requires:
  - houghton-groups-have-at-most-exponential-dehn-function
artifacts:
  - research/artifacts/zp-houghton-pour-doubling-2026-09-18.md
  - research/artifacts/zp-houghton-three-rays-2026-09-18.md
  - research/artifacts/zp-houghton-pours-2026-09-17.md
  - experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.py
  - experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.out
---

The complete proof is §§1–3 (Lemmas 1–3 and Proposition 5) of
`research/artifacts/zp-houghton-pour-doubling-2026-09-18.md`.

- **Doubling.** `Δ` is the doubling endomorphism of Lemma B.1 of
  `research/artifacts/zp-houghton-three-rays-2026-09-18.md`, with the route ray `c` as
  its special ray. Lemma B.1 is quoted verbatim, up to renaming the rays.
  - `Δ(λ_ac) = λ_ac^2` and `Δ(λ_cb) = λ_cb^2` exactly, so the lift of the literal pour
    word of size `m` is the literal pour word of size `2m`.
  - The two-ray letters have two-ray images, e.g. `Δ(λ_ab) = λ_ab^2 τ_b`.
- **Area transfer.** Lemma B.2 there, quoted verbatim, gives
  `Area(Δ̂ w) <= K Area(w)`. This uses only the finiteness of `P_3`. `P_3` is Lee's
  presentation (quoted in `houghton-groups-have-at-most-exponential-dehn-function`)
  plus the finitely many letters and relators of the pours note §0.
- **Odd step.** Conjugation by `λ_ca` sends each two-ray letter to a two-ray word of
  length `<= 3`, via a relator of length `<= 6` in `Q`. So `m -> 2m+1` costs
  `2|N_(2m)| + 1`.
- **Recursion.** `A(2m) <= K A(m)` and `A(2m+1) <= A(2m) + 2|N_(2m)| + 1`, with
  `|N_m| <= 32^(⌊log_2 m⌋) <= m^5`. Hence `A(m) <= 4(1 + log_2 m) m^(5 + log_2 K)`.

The script checks the following:

- the four exact doublings;
- the substitution table, by breadth-first search, rechecked at larger depth;
- `N_m = λ_ac^m λ_cb^m` as elements for `m <= 40`;
- the exact lengths `|N_m|` for `m <= 4096`, giving an empirical exponent of about
  `3.1`;
- the homomorphism property on random words.

The area recursion itself consists of the explicit rewrites listed in the proof.
