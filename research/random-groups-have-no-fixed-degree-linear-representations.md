---
rg: 2
id: random-groups-have-no-fixed-degree-linear-representations
kind: claim
title: Gromov random groups at positive density a.a.s. have no linear representation of fixed degree with image larger than two, over any field
distinct_from:
  density-random-groups-no-small-nondegenerate-almost-reps: that bounds approximate unitary representations of dimension up to about (2m-1)^(dl/2) in the cyclically reduced model; this is exact representations of one fixed degree, over every field at once, in the reduced-word model
  linear-quotient-exclusion-lifts-from-char-zero: that decides, for one finitely presented group and one degree, in which characteristics nontrivial projective representations exist; this says a random presentation has none of fixed degree, a.a.s., in every characteristic
artifacts:
  - research/artifacts/solve-hyperbolic-rf-simple-quotients-2026-09-13.md
---

**ESTABLISHED** by literature import `random-groups-no-fixed-degree-representations-citation`.

**Model** (Kozma–Lubotzky's, Gromov's density model).
- Fix `m >= 2` and `d >= 0`. Let `S_l` be the set of reduced words of length `l` in
  `x_1^{±1}, …, x_m^{±1}`.
- Take `⌊|S_l|^d⌋` elements of `S_l`, uniformly, independently and with repetitions, as
  relators `R`, and put `Γ = <x | R>`.
- A property holds a.a.s. if its probability tends to 1 as `l → ∞`.

**THEOREM** (Kozma–Lubotzky, arXiv:1810.01529, Theorems `thm:d` and `thm:poly`).
1. Let `k >= 1`, `m >= 2` and `d > 0`. A.a.s., for every field `F` and every homomorphism
   `ρ: Γ -> GL_k(F)`, `|ρ(Γ)| <= 2`.
2. Polynomially many relators already suffice. With at least `(3l)^(7 m^2 k^4)` independent
   uniform reduced words of length `l`, the probability that some field `F` and some `ρ`
   have `|ρ(Γ)| > 2` tends to 0 as `l → ∞`.
3. For a single algebraically closed field `F` and `l > l_0(k, m)`, `u >= 15 m^3 k^4 log l`
   relators give probability at most `exp(−c u/(m k^2))`, with `c` an absolute constant.

**Remarks from the source.**
- For odd `l`, a.a.s. `ρ(Γ) = {1}`. For even `l`, `Z/2` is always a quotient.
- The degree `k` is fixed. For `d < 1/6`, `Γ` is a.a.s. linear over `Z` (Agol,
  Ollivier–Wise), in degree growing with `l`.

The proof, not re-derived here, breaks irreducible components of the representation
variety one relator at a time. It uses `lem:half` (imported as
`nonbacktracking-walks-on-regular-multigraphs-return-rarely`), Bézout's theorem, and an
effective Nullstellensatz for the large characteristics.
