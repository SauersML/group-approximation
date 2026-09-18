---
rg: 2
id: houghton-h4-polynomial-dehn-via-h3-ray-stabilizers
kind: route
title: "H_3 polynomial implies H_4 polynomial: run the path-word proof with n = 4, bounding pour route changes by H_3 discs"
target: houghton-group-h4-has-polynomial-dehn-function
requires:
  - houghton-group-h3-has-polynomial-dehn-function
  - houghton-four-ray-pour-route-change-bounded-by-h3-dehn
  - houghton-dehn-polynomially-equivalent-to-commutation-area
artifacts:
  - research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md
  - research/artifacts/zp-houghton-five-rays-2026-09-17.md
  - research/artifacts/zp-houghton-pours-2026-09-17.md
---

The proof is Theorem 4 of `research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`.

- **Bound on W.** If `δ_(H_3)(x) ≼ x^d`, then
  `houghton-four-ray-pour-route-change-bounded-by-h3-dehn` gives `W_4(m) ≼ m^(3d)`.
- **Path-word proof.** Run Theorem C of
  `research/artifacts/zp-houghton-five-rays-2026-09-17.md` with `n = 4` and
  `β = 3d >= 6`, using that bound in place of its Proposition B.
- **Rays.** Theorem C uses `n >= 5` only through `W`. Every other step of §§2–6 of the
  six-ray note chooses at most four distinct rays. The artifact re-checks each ray
  choice for `n = 4`: Lemma 2.1, Theorem 3.1, Proposition 4.1 (ii)–(iv), Lemma 4.2,
  and §§5–6.
- **Result.** `δ_(H_4) ≼ x^(6+3d)`.

Sharper: only the single family `A_3(m) = Area_(H_3)(E^c_(a,b)(m) N_(a,b)(m)^(-1))` is
needed (Remark 3.1). `A_3 ≼ m^D` already gives `δ_(H_4) ≼ x^(6+D)`.

With the ray-count route `houghton-polynomial-dehn-by-ray-count`, this leaves
`houghton-group-h3-has-polynomial-dehn-function` as the only open prerequisite of
`houghton-groups-have-polynomial-dehn-function`.
