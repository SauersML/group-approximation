---
rg: 2
id: penrose-derived-full-group-homology-proof
kind: route
title: Li's Penrose groupoid homology Z^8, Z^5, Z fed through the H_2 filtration, and Hopf's formula for relation invariants
target: penrose-derived-full-group-homology-is-finitely-generated
requires:
  - derived-full-group-h2-filtered-by-mod-two-groupoid-homology
  - li-derived-full-group-homology-is-k-theory-cover
  - penrose-tiling-group-is-an-amenable-orbit-full-group
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

The artifact, Sections 5–6, gives the same argument.

1. **The groupoid.** ChJN (arXiv:1602.04255, lines 336–372, read on MSI) defines `𝒫` as the
   homeomorphisms of the transversal `𝒯` that are locally equal to the moves `F_{A,v_1,v_2}`.
   - `𝒯` consists of pointed Penrose rhombus tilings, with sides parallel to
     `e^{kπi/5} R`, up to translation.
   - So `𝒫 = F(G_𝒫)`, where `G_𝒫` is the groupoid of germs of these moves. This is the reduction
     of the translation-hull groupoid to the vertex transversal.
2. **Hypotheses.** Penrose tilings are aperiodic, repetitive and FLC. So `G_𝒫` is minimal, with
   Cantor unit space and comparison (`li-derived-full-group-homology-is-k-theory-cover`, item 4,
   line 839).
3. **Homology.** Item 4 gives `H_*(G) = Z^8, Z^5, Z, 0, ...` for Kellendonk's tiling groupoid of
   the classical Penrose tiling.
   - `G_𝒫` is equivalent to it. Take the transversal of vertices together with tile punctures.
     Both the vertex set and the puncture set are clopen in it and meet every orbit, so each
     reduction is equivalent to the union groupoid.
   - The rhombus and kite–dart versions are mutually locally derivable, so their tiling groupoids
     are equivalent.
   - Groupoid homology is Morita invariant (Li line 3043, citing Matui §3).
   - So `H_*(G_𝒫) = Z^8, Z^5, Z, 0, ...`.
   - Caveat: which classical version Li's line 3282 means was not checked.
4. **Mod 2.** Universal coefficients give `H_0(G_𝒫; Z/2) = (Z/2)^8` and
   `H_1(G_𝒫; Z/2) = (Z/2)^5`, since `Tor(Z^8, Z/2) = 0`. Also
   `H_2(G_𝒫; Z/2) = Z/2 ⊕ Tor(Z^5, Z/2) = Z/2`, and `H_3 = 0`.
5. **Item 1.** Apply Theorem 1 of `derived-full-group-h2-filtered-by-mod-two-groupoid-homology`.
   - `F_0 = (Z/2)^8 / d^2(Z/2)` has order `2^7` or `2^8`.
   - `F_1/F_0 = (Z/2)^5`.
   - `F_2/F_1 = ker(Z -> (Z/2)^8) ≅ Z`.
   - `F_1` has exponent at most 4, and the free quotient splits off.
6. **Item 2.** Corollary 2(c), with every `H_p(G_𝒫)` finitely generated.
7. **Item 3.**
   - For `w ∈ N` and `x ∈ 𝒯`, the marked vertex traces a closed polygon in `C`. Let `A(w, x)` be
     its signed area. It is locally constant in `x`.
   - `μ` is the invariant probability of `penrose-tiling-group-is-an-amenable-orbit-full-group`,
     transported to `𝒯` by ChJN's isomorphism `𝒫 ≅ [[Lambda ~ X]]`. Put
     `alpha(w) = ∫ A(w, x) dμ`.
   - **Additivity.** For `w_1, w_2 ∈ N`, the loop of `w_1 w_2` at `x` is the loop of `w_2` at
     `x`, then the loop of `w_1` at `x`. So `alpha` is additive on `N`.
   - **Conjugation.** The loop of `u w u^{-1}` at `x` is the loop of `w` at `u^{-1} x`, with a
     tail that cancels. Invariance of `μ` gives `alpha(u w u^{-1}) = alpha(w)`.
   - So `alpha`, like any conjugation-invariant homomorphism `N -> A`, factors through `N/[F,N]`.
   - Hopf's formula gives `0 -> H_2(D(𝒫)) -> N/[F,N] -> N[F,F]/[F,F] -> 0`, with the right-hand
     term a subgroup of `Z^{|S|}`. By item 1, `N/[F,N]` is finitely generated, and so is its image. ∎
