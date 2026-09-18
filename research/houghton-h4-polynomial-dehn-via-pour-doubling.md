---
rg: 2
id: houghton-h4-polynomial-dehn-via-pour-doubling
kind: route
title: Run the path-word proof with n = 4, bounding pour route changes by the doubled two-ray pour words, with no input about H_3
target: houghton-group-h4-has-polynomial-dehn-function
requires:
  - houghton-four-ray-pour-route-change-is-polynomial
  - houghton-dehn-polynomially-equivalent-to-commutation-area
artifacts:
  - research/artifacts/zp-houghton-pour-doubling-2026-09-18.md
  - research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md
  - research/artifacts/zp-houghton-five-rays-2026-09-17.md
  - research/artifacts/zp-houghton-pours-2026-09-17.md
---

The proof is Theorem 7 of `research/artifacts/zp-houghton-pour-doubling-2026-09-18.md`.
It is Theorem 4 of `research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`
with the unconditional bound on `W_4` in place of its Theorem 3.

- **Bound on W.** `houghton-four-ray-pour-route-change-is-polynomial` gives
  `W_4(m) ≼ m^β` for some `β > 5`.
- **Path-word proof.** Run Theorem C of
  `research/artifacts/zp-houghton-five-rays-2026-09-17.md` with `n = 4`. The four-ray
  note (Theorem 4, quoted verbatim in the artifact) shows two things:
  - Theorem C uses `n >= 5` only through `W`. It re-checks every ray choice of the
    six-ray note for `n = 4`: Lemma 2.1, Theorem 3.1, Proposition 4.1 (ii)–(iv),
    Lemma 4.2, and §§5–6.
  - Its bookkeeping needs only `W ≼ m^β` with `β >= 2`.
- **Commutation reduction.** Theorem C's other input is
  `houghton-dehn-polynomially-equivalent-to-commutation-area`, which holds for every
  `n >= 3`.
- **Result.** `δ_(H_4)(x) ≼ x^(6+β)`. The exponent is inexplicit, because `β` contains
  `log_2` of the area-transfer constant of the doubling on Lee's relators.

Unlike `houghton-h4-polynomial-dehn-via-h3-ray-stabilizers`, this route needs nothing
about `houghton-group-h3-has-polynomial-dehn-function`.
