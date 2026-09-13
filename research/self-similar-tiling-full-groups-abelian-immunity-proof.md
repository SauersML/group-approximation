---
rg: 2
id: self-similar-tiling-full-groups-abelian-immunity-proof
kind: route
title: Assemble the recognizability cohomology bound, the Z^2 criterion and the Li filtration for the whole class
target: self-similar-tiling-full-groups-abelian-obstructions-vanish
requires:
  - recognizable-self-similar-z2-subshifts-have-finite-cohomology
  - z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite
  - derived-full-group-h2-filtered-by-mod-two-groupoid-homology
  - li-derived-full-group-homology-is-k-theory-cover
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
---

The argument is that of `labbe-derived-full-group-homology-proof`, with Labbé's specific morphism
replaced by the class hypothesis. The instance proof already used only recognizability, expansiveness,
`X = closure_σ(ω(X))`, freeness and minimality, all of which are class hypotheses here.

1. **Finite cohomology.** `recognizable-self-similar-z2-subshifts-have-finite-cohomology` gives, for
   every `m >= 2`, `|H^1(Z^2; C(X, Z/m))|` and `|H^2(Z^2; C(X, Z/m))|` finite, bounded by pattern
   counts of `X`.
2. **Item 1.** `z2-derived-full-group-h2-fg-iff-mod-two-cohomology-finite`, with `m = 2`, gives
   `H_2(Gamma) ≅ Z ⊕ T`, `T` a finite 2-group of exponent at most 4. Its hypotheses (free minimal
   `Z^2` Cantor action) are class hypotheses.
3. **Item 2.** Let `G = Z^2 ⋉ X`, `K = K(B_G)`, `Y` the universal cover of `Ω^∞_0 K`.
   - `li-derived-full-group-homology-is-k-theory-cover`, items 2–3: `H_*(Gamma) ≅ H_*(Y)`, and for
     `j >= 2`, `π_j(Y) = π_j(K)` is filtered by `E^2_{p,q} = H_p(G; π_q(S))`, `p + q = j`.
   - Duality `H_p(G; A) = H^{2-p}(Z^2; C(X, A))` restricts to `p <= 2`.
   - `q = 0` contributes only `(2,0) = H_2(G) = Z`; every `q >= 1` piece is finite by step 1
     applied to the finite group `π_q(S)`.
   - So all `π_j(Y)` are finitely generated and `π_1(Y) = 0`. Serre's mod-`C` Hurewicz theorem
     gives `H_j(Y) = H_j(Gamma)` finitely generated.
4. **Item 3.** The invariant probability `μ` (Markov–Kakutani for `Z^2`, full support by minimality)
   is `Gamma`-invariant. The mean signed area `alpha(w) = ∫ A(w, x) dμ` is additive and
   conjugation-invariant, so it factors through `N/[F,N]`, which by Hopf's formula is an extension of
   a subgroup of `Z^{|S|}` by `H_2(Gamma)`, hence finitely generated. The same holds for every
   conjugation-invariant homomorphism on `N`. ∎
