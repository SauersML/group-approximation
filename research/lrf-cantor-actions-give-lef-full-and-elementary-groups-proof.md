---
rg: 2
id: lrf-cantor-actions-give-lef-full-and-elementary-groups-proof
kind: route
title: Proof that LRF is equivalent to a combinatorial matricial model, which makes full groups and elementary groups LEF
target: lrf-cantor-actions-give-lef-full-and-elementary-groups
requires:
  - simple-rings-with-local-matrix-models-are-matricial
  - steinberg-algebra-simple-iff-minimal-effective
  - full-group-units-embed-in-steinberg-algebras
  - crossed-products-are-transformation-steinberg-algebras
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/un-full-groups-bridge-2026-09-13-part1.md
---

Full proof in the artifact, §2. Outline:

1. **(i) ⇒ (ii').**
   - Take `F_n = S_n^3` for symmetric windows `S_n`, with partial actions `β_n` on `F_n`.
   - Set `ψ_n(Σ f_g u_g) = Σ D_n(f_g) P_n(g)` on normal forms supported in `S_n`.
   - Multiplicativity on the window uses only `β_n(g)β_n(h) = β_n(gh)` for `g, h, gh ∈ F_n` and `ε_n`-intertwining at
     `g^(-1) ∈ F_n`. This is `un-measure`'s Theorem A computation with a partial action.
   - `R` is simple (minimal effective groupoid), so Lemma S makes `Ψ` injective.
   - Bisection units go to `D(1_(r(B)))P(g)` sums with disjoint row supports and, for small `ε_n`, disjoint column
     supports. So the model is combinatorial.
2. **(ii) ⇒ (i).**
   - Invertible partial permutation matrices are permutations, which gives `β_n(g)` from `Ψ(u_g)`. Products are exact
     on `F`, `ω`-a.e.
   - Idempotent partial permutation matrices are diagonal. So clopen units give a partition `E_n(U)` of the model set,
     with `β_n(g)E_n(U) = E_n(α(g)U)`.
   - An injective placement `ζ` of `E_n(U)` into the infinite atom `U` gives `ε`-intertwining.
3. **(a).**
   - Full bisection units are invertible with invertible images, hence permutations `ω`-a.e.
   - `Ψ` is injective, so `[[α]] ↪ ∏_ω Sym(N_n)`, which gives LEF.
4. **(b).** `GL_m(R) ↪ ∏_ω GL_(mN_n)(F_q)`. Property (T) via Ershov–Jaikin-Zapirain.

**Model tests** (artifact §2):
- `Γ = Z` recovers Grigorchuk–Medynets and the Pestov ring.
- The Cuntz groupoid admits no matricial model at all.
- A non-simple ring breaks Lemma S, as it must.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part2.md`): PASS with the domain reading: the window formula is used on supports in F_n = S_n^3, not only S_n.**
