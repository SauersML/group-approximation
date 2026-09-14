---
rg: 2
id: subshift-elementary-group-lef-growth-complexity-bounds-proof
kind: route
title: Rauzy-walk periodic models bound the LEF growth above; commuting perfect cylinder subgroups and transported unitriangular tower relations bound it below
target: subshift-elementary-group-lef-growth-complexity-bounds
requires: [simple-kazhdan-lef-group-from-minimal-subshift]
artifacts:
  - research/artifacts/sk-lef-growth-bounds-2026-09-13-part1.md
  - research/artifacts/sk-lef-growth-bounds-2026-09-13-part2.md
---

The required claim `simple-kazhdan-lef-group-from-minimal-subshift` gives that `G_X` is infinite with (T). So `G_X` is non-amenable and has exponential growth, which is the bound `λ^r`. The artifacts prove the rest.

- **Upper bound (part 1, Theorem A).**
  - Entries of ball elements have `u`-exponents `≤ r` and windows in `[−r, r]`. A product of two ball elements uses windows in `[−2r, 2r]`.
  - Take a cyclic word `y` of length `N` whose cyclic `(4r+1)`-windows are exactly `L_(4r+1)(X)`. The model `Σ f_j u^j ↦ Σ D_y(f_j) P^j` maps into `GL_(3N)(F_2)`, and it is injective on the ball because `N ≥ 4r+2`.
  - The note's return construction gives `N ≤ 2R_X(n)`.
  - A covering closed walk in the Rauzy graph gives `N ≤ (p_X(n)+1) p_X(n−1)`.
  - For Sturmian `X`, the Rauzy graph is one cycle plus one ear, so `N ≤ 2n+2`.
- **Lemma 0.** A ball-injective partial homomorphism preserves every relation of length `≤ r` among the generators.
- **Lemma 1.** Conjugating by `w_ik(u) w_ik(1) = diag(u, u^(-1))` multiplies an entry by `u^(±1)`. So `|e_ij(u^a r u^b)| ≤ |e_ij(r)| + 12(|a|+|b|)`.
- **Lemma 2.** `|e_ij(e_[w])| ≤ 25·4^h` for a cylinder of length `2^h`, by the commutator identity and Lemma 1.
- **Theorem B (B2).**
  - Put `x^v_ij = e_ij(e_[v])` for the words `v` of length `2^h`.
  - In a finite model, their images generate pairwise commuting perfect groups `P_v ≠ 1`.
  - The multiplication map has kernel inside `∏ Z(P_v)`, and a nontrivial perfect group has order `≥ 60`.
- **Theorem C (part 2).**
  - The tower copy `U_d(F_2) ⊆ H_W` has transvections of length `≤ 4(κ + 24m)`.
  - Lemma 3 shows, by a height filtration, that the Steinberg relations present exactly `U_d(F_2)`.
  - A nontrivial kernel would meet the centre `⟨I + E_1d⟩`, whose generator survives by injectivity.
