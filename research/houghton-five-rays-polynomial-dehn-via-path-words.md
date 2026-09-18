---
rg: 2
id: houghton-five-rays-polynomial-dehn-via-path-words
kind: route
title: Run the six-ray path-word proof with the one-auxiliary-ray pour bound W ≼ m^(log_2 5)
target: houghton-groups-with-five-or-more-rays-have-polynomial-dehn
requires:
  - houghton-dehn-polynomially-equivalent-to-commutation-area
  - houghton-five-ray-pour-route-change-is-polynomial
artifacts:
  - research/artifacts/zp-houghton-five-rays-2026-09-17.md
  - research/artifacts/zp-houghton-pours-2026-09-17.md
---

The complete proof is Theorem C of
`research/artifacts/zp-houghton-five-rays-2026-09-17.md`. It runs §§2–6 of
`research/artifacts/zp-houghton-pours-2026-09-17.md` (the six-ray note) with `n = 5`.

- **Rays.** In the six-ray note, `n >= 6` enters only through its Lemma 1.2. Every
  other step there chooses at most four distinct rays. Theorem C checks this lemma
  by lemma.
- **Inputs.** Lemma 1.2 and Proposition 1.3 are replaced by
  `houghton-five-ray-pour-route-change-is-polynomial` (`W ≼ m^β`, `β = log_2 5`).
  Lemma 1, Lemma 3 and Step 2 of the 09-13 note are valid for every `n >= 3`, as in
  `houghton-dehn-polynomially-equivalent-to-commutation-area`.
- **Exponents.** `R, F, E ≼ k^β`. The edge and letter conjugation lemmas cost
  `≼ R^(2+β)`. Normalizing costs `≼ L^(5+β)`, and eliminating costs `≼ L^(6+β)`.
