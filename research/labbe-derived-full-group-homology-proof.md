---
rg: 2
id: labbe-derived-full-group-homology-proof
kind: route
title: Labbé's recognizable morphism gives finite mod-m cohomology, which the Li filtration turns into finitely generated homology of the derived full group
target: labbe-shift-derived-full-group-homology-is-finitely-generated
requires:
  - recognizable-self-similar-z2-subshifts-have-finite-cohomology
  - z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite
  - derived-full-group-h2-filtered-by-mod-two-groupoid-homology
  - li-derived-full-group-homology-is-k-theory-cover
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-labbe-2026-09-13.md
---

**Source for the hypotheses.** Labbé, arXiv:1802.03265. The TeX source `article1.tex` was read on
MSI at `/scratch.global/sauer354/fpsz2/src/1802.03265.d/` on 2026-09-13.
- Proposition `prop:pre-main`, lines 2269–2280, verbatim: "The d-dimensional morphism
  `ω : Omega_U -> Omega_U` defined as `ω = α ∘ β ∘ γ` is expansive, recognizable in `Omega_U` and
  satisfies `Omega_U = ω(Omega_U) ∪ σ^{e_1} ω(Omega_U) ∪ σ^{e_2} ω(Omega_U) ∪ σ^{e_1+e_2} ω(Omega_U)`."
- Definitions: morphism (lines 813–823), expansive (line 884), recognizable (lines 1134–1143).

1. **Theorem 6 applies.** `Omega_U` is a subshift of `U^{Z^2}`, and `ω` is an expansive
   2-dimensional morphism `Omega_U -> Omega_U`, recognizable in `Omega_U`.
   - The displayed equation gives `Omega_U ⊆ closure_σ(ω(Omega_U)) ⊆ Omega_U`.
   - So `recognizable-self-similar-z2-subshifts-have-finite-cohomology` applies. For every
     `m >= 2`, `H^1(Z^2; C(Omega_U, Z/m))` and `H^2(Z^2; C(Omega_U, Z/m))` are finite.
2. **Item 1.** `Z^2` acts freely and minimally on the Cantor set `Omega_U`
   (`minimal-aperiodic-wang-shift-exists`).
   - With `m = 2`, `z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite` gives
     `H_2(Gamma) ≅ Z ⊕ T`, with `T` a finite 2-group of exponent at most 4.
3. **Item 2.** Put `G = Z^2 ⋉ Omega_U`, `K = K(B_G)`, and let `Y` be the universal cover of
   `Ω^∞_0 K`.
   - By `li-derived-full-group-homology-is-k-theory-cover`, items 2–3, `H_*(Gamma) ≅ H_*(Y)`, and
     `π_j(Y) = π_j(K)` for `j >= 2` is filtered by `E^∞_{p,q}` with `p + q = j` and
     `E^2_{p,q} = H_p(G; π_q(S))`.
   - By duality `H_p(G; A) = H^{2-p}(Z^2; C(Omega_U, A))`, so `p <= 2`.
   - For `q >= 1`, `π_q(S)` is a finite abelian group `⊕ Z/m_i`.
     - For `p = 0, 1`, `H_p(G; π_q(S))` is a finite sum of the finite groups of step 1.
     - For `p = 2` it is `H^0 = π_q(S)`, which is finite.
   - For `q = 0` and `j >= 2`, only `(p,q) = (2,0)` occurs, with `H_2(G) = Z`.
   - So every `π_j(Y)`, `j >= 2`, is finitely generated, and `π_1(Y) = 0`.
   - Serre's mod-`C` Hurewicz theorem, for finitely generated abelian groups and simply connected
     `Y`, makes every `H_j(Y) = H_j(Gamma)` finitely generated.
4. **Item 3.**
   - `Z^2` is amenable, so there is an invariant probability `μ` on `Omega_U`. It is invariant
     under `Gamma`, because elements of the full group move points within `Z^2`-orbits by
     piecewise translations.
   - For `w ∈ N` and `x ∈ Omega_U`, let `A(w, x)` be the signed area of the closed lattice loop
     traced in the orbit `Z^2 · x ≅ Z^2`.
   - `alpha(w) = ∫ A(w, x) dμ` is additive on `N`: the loop of `w_1 w_2` at `x` is the loop of
     `w_2`, then the loop of `w_1`.
   - `alpha` is conjugation-invariant: `A(u w u^{-1}, x) = A(w, u^{-1} x)`, and `μ` is invariant.
   - So `alpha`, and every conjugation-invariant homomorphism on `N`, factors through `N/[F,N]`.
   - Hopf's formula gives `0 -> H_2(Gamma) -> N/[F,N] -> N[F,F]/[F,F] <= Z^{|S|}`. With item 1,
     `N/[F,N]` is finitely generated. ∎
