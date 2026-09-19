---
rg: 2
id: houghton-h3-five-families-via-path-words
kind: route
title: Rerun the six-ray path-word proof for three rays, keeping every step that needs a spare ray as a black-box family
target: houghton-h3-dehn-polynomial-iff-five-three-ray-families
requires:
  - houghton-dehn-polynomially-equivalent-to-commutation-area
artifacts:
  - research/artifacts/zp-houghton-three-rays-2026-09-18.md
  - research/artifacts/zp-houghton-pours-2026-09-17.md
  - research/artifacts/zp-houghton-dehn-2026-09-13-part1.md
---

The complete proof is Theorem A (§A) of
`research/artifacts/zp-houghton-three-rays-2026-09-18.md`. It reruns §§4–6 of
`research/artifacts/zp-houghton-pours-2026-09-17.md` (the six-ray note) with `n = 3`.

1. **Lower bound.** Every family word is null-homotopic of length `O(k)`, so
   `Φ(L) <= δ(CL)`.
2. **Edge relations (A.2).** The six-ray note proves Proposition 4.1 case by case.
   The cases (E1), (E3), (E4), (E2)(i) and (E2)(v) use no spare ray. For `n = 3` they
   cost `O(R)` plus `F_3`. The cases (E2)(ii)–(iv) reroute to fresh rays in the six-ray
   note; here they are the families `B_3` and `C_3`. So `E(R) <= Φ(R) + CR`.
3. **Letters on edges (A.3).** Lemma 4.2, case 1, rerouted to a fourth ray; here it is
   `D_3`. The other cases are free identities plus two reroutes `R_3`. So
   `Λ(R) <= 2Φ(R+1) + 4R + 4`.
4. **Path words (A.4).** Lemmas 5.1–5.6 and Corollary 5.3 choose no ray. The top
   detour has `q <= n - 1 = 2`, and in Lemma 5.6 the auxiliary vertex `(w,1)` is
   forced. So they hold with `Ē` and `Λ̄`, and Lemma 5.6 costs
   `Γ(R) <= C R^2 (Φ(R+2) + R)`.
5. **Total.** Sort and translate (Lemma 3, Lemma 1 of the 09-13 note, valid for
   every `n >= 3`, from `houghton-dehn-polynomially-equivalent-to-commutation-area`)
   at cost `O(L^3)`. Normalize at cost `M ℓ Γ(R) ≼ L^5 Φ + L^6`. Eliminate with
   `3R · M` carry-and-merge moves, each `≼ R^3 Ē`, for `≼ L^6 (Φ(L+C) + L)` in total.
