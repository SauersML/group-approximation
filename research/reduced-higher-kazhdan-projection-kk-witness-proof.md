---
rg: 2
id: reduced-higher-kazhdan-projection-kk-witness-proof
kind: route
title: Feed the Li--Nowak--Pooya higher Kazhdan projection into the matrix-to-scalar passage and the selfless trace lemma
target: reduced-higher-kazhdan-projection-kk-witness
requires:
  - fractional-matrix-trace-gives-projection-in-g-star-z
  - selfless-projection-traces-equal-k0-trace-image
  - lueck-surjective-assembly-traces-lie-in-lambda-g
  - subgroup-average-projections-give-no-reduced-bc-obstruction
---

**Literature input.** Kang Li, Piotr W. Nowak and Sanaz Pooya, *Higher Kazhdan projections, ℓ_2-Betti
numbers and Baum-Connes conjectures*, arXiv:2006.09317v2, read from the arXiv PDF on 2026-09-12.
Verbatim:
- **Definition 4:** "A Kazhdan projection in degree n is a projection p_n = p_n^* = p_n^2 ∈ M_(k_n)(C*_F(G))
  such that for every unitary representation π ∈ F the projection π(p_n) is the orthogonal projection
  C^n(G,π) → ker π(Δ_n)."
- **Proposition 5:** "Assume that Δ_n ∈ M_k(C*_F(G)) (respectively, Δ_n^+, Δ_n^-) has a spectral gap.
  Then the Kazhdan projection p_n (respectively, the partial Kazhdan projections p_n^+, p_n^-) exist in
  the C*-algebra M_(k_n)(C*_F(G))."
- **Proposition 7:** "Assume that Δ_n has a spectral gap in M_k(C*_r(G)). Then τ_*([p_n]) = β^n_(2)(G).
  In particular, if β^n_(2)(G) ≠ 0 then [p_n] ≠ 0 in K_0(C*_r(G))."
- **Proposition 1:** "Let G be of type F_(n+1). Assume that 0 is isolated in the spectrum of
  Δ_n ∈ M_k(C*_r(G)). If the Baum-Connes assembly map K_0^G(E̲G) → K_0(C*_r(G)) is surjective then
  β^n_(2)(G) ∈ Λ^G. In particular, if G is torsion-free then β^n_(2)(G) ∈ Z." Its proof there cites
  Lück's Theorem 0.3, imported as `lueck-surjective-assembly-traces-lie-in-lambda-g`.
- **§1.5:** "In case of an infinite group G the projection λ(p_0) ∈ C*_r(G) is always 0 since the kernel
  of λ(Δ_0) consists precisely of constant functions in ℓ_2(G)."
- **§1.5.1:** "Then for F_n the projection p_1 ∈ M_k(C*_r(F_n)) exists and gives rise to a non-zero
  class in K-theory C*_r(F_n)."

Here "spectral gap" means `spec(Δ_n) ⊆ {0} ∪ [ε, ∞)` for some `ε > 0` (p. 2 of the paper). The
subgroup statement is `subgroup-average-projections-give-no-reduced-bc-obstruction`, part 1.

**Items 1 and 2.** `p_n ∈ M_k(C*_r G)` is a projection with `τ_*(p_n) = β^n_(2)(G) ∉ Z`
(Propositions 5 and 7).
- Item 1 of `fractional-matrix-trace-gives-projection-in-g-star-z` gives a projection `e ∈ C*_r(G * Z)`
  with `τ(e) = β^n_(2)(G) - floor(β^n_(2)(G)) ∈ (0,1)`. Item 2 there makes `G * Z` torsion-free.
- If `C*_r(G)` is selfless, `selfless-projection-traces-equal-k0-trace-image` realizes the class
  `[p_n] - floor(β^n_(2)(G))[1]`, whose trace lies in `(0,1)`, by a projection of `C*_r(G)`.

**Item 3.** `Δ_n ∈ M_k(Z[G]) ⊆ M_k(Q[G])`. Its kernel on `ℓ^2(G)^k` is the range of `p_n`, of von
Neumann dimension `τ_*(p_n) = β^n_(2)(G)` (Proposition 7). A non-integer value contradicts Strong
Atiyah over `Q` for the torsion-free `G`.

**Item 4.** This is the contrapositive of Proposition 1 for torsion-free `G`.

**Model tests.**
- `F_m` has a finite `K(F_m,1)`, and `β^1_(2)(F_m) = m - 1`: §1.5.1 supplies the gap, and the value
  is an integer.
- In degree `0` for infinite `G`, §1.5 gives `λ(p_0) = 0`.
