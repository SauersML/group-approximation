---
rg: 2
id: houghton-dehn-commutation-area-reduction-proof
kind: route
title: Sort translation letters, then eliminate points of the finitary kernel one at a time
target: houghton-dehn-polynomially-equivalent-to-commutation-area
requires: []
artifacts:
  - research/artifacts/zp-houghton-dehn-2026-09-13-part1.md
---

Complete proof in `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`,
§§1–6. Outline:

1. `A(L) <= δ(2L+2)`, since `[z,α]` is a null-homotopic word of length `2L+2`.
2. Every transposition of points of depth `<= R` equals `α^(c_τ)` for a word
   `c_τ` of length `O(R)`, built from the shifts `λ_(a,b)` and a third ray
   (Lemma 2, using `n >= 3`).
3. A null-homotopic word of length `L` is sorted by index of its translation
   letters with `O(L^2)` applications of conjugates of Lee's relator
   `[g_i,g_j] = α`. Each swap spawns a conjugate of `α` that is pushed to the right
   freely. The sorted translation word is trivial because the exponent sums vanish.
   What remains is a product of `M = O(L^2)` conjugates of `α` by words of length
   `O(L)` (Lemma 3).
4. Each factor is a transposition of points of depth `O(L)`. Normalizing to
   canonical conjugates costs `A(O(L))` per factor. Eliminating the `O(L)` points
   one at a time by carry-and-merge uses `O(L)·M` relations
   `Can(ρ)Can(σ)Can(ρ) = Can(ρσρ)`. Each is freely conjugate to a commutator
   `[z,α]` with `|z| = O(L)` and `z` centralizing `α`, so it costs at most
   `A(O(L)) + 1`.
5. Total: `δ(L) <= C L^3 (A(CL) + 1)`.
