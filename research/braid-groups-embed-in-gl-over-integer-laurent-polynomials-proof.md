---
rg: 2
id: braid-groups-embed-in-gl-over-integer-laurent-polynomials-proof
kind: route
title: Specialize the Cohen–Wales parameter r to the unit (3 - sqrt 5)/2 and restrict scalars
target: braid-groups-embed-in-gl-over-integer-laurent-polynomials
requires: []
---

**Source.** A. M. Cohen and D. B. Wales, *Linearity of Artin groups of finite
type*, arXiv:math/0010204v2. Text extracted from the arXiv PDF on MSI
(ghostscript) on 2026-09-13, page 2:

> "The coefficients of our representation will be taken in the ring
> Z[r;t;r−1;t−1], and we write V for the free module over that ring with
> generators x_β indexed by β ∈ Φ+."
>
> "Theorem 1.2. Let B be an Artin group of type A, D, E. Then, for each k ∈
> {1;...;n} and each β ∈ Φ+, there is a polynomial T_k;β in Z[r] such that the
> following map on the generators of B determines a representation of B on V.
> s_k ↦ σ_k = τ_k + tT_k [...] If r is specialized to a real number r_0,
> 0 < r_0 < 1, in V ⊗ R, we obtain a faithful representation of B on the
> resulting free R[t;t−1]-module V_1 with basis x_β (β ∈ Φ+)."

Page 1: "The braid group on n+1 braids is the Artin group of type A_n". §4 opens
with the same specialization ("we specialize r to a real number r_0 with
0 < r_0 < 1 in V ⊗ R to obtain V_1, the free module over R[t;t−1]").

**Derivation.**

1. Let `phi = (1 + sqrt 5)/2` and `r_0 = phi^{-2} = (3 - sqrt 5)/2 ≈ 0.382`. Then
   `0 < r_0 < 1`, and `r_0` is a unit of `O = Z[phi]`, since
   `phi^2 = (3 + sqrt 5)/2` and `(3 + sqrt 5)(3 - sqrt 5)/4 = 1`.
2. `rho` is a representation of the group `B` on the free
   `Z[r^{±1}, t^{±1}]`-module `V`, so the images of the generators and their
   inverses have entries in `Z[r^{±1}, t^{±1}]`. The substitution
   `r -> r_0` is a ring homomorphism `Z[r^{±1}, t^{±1}] -> O[t^{±1}]`, because
   `r_0` is a unit. It gives a homomorphism `rho_0: B -> GL_N(O[t^{±1}])` with
   `N = |Φ^+|`.
3. `O ⊂ R` through the real embedding with `sqrt 5 > 0`, so
   `O[t^{±1}] ⊂ R[t^{±1}]`, and composing `rho_0` with this inclusion gives the
   representation of Theorem 1.2 at `r_0`. That representation is faithful, so
   `rho_0` is injective.
4. `O` is free over `Z` with basis `{1, phi}`. Left multiplication gives an
   injective ring homomorphism `O -> M_2(Z)`. Apply it coefficientwise to
   Laurent polynomials, then entrywise, to get an injective ring homomorphism
   `M_N(O[t^{±1}]) -> M_(2N)(Z[t^{±1}])`. It preserves inverses, so it maps
   `GL_N` into `GL_(2N)`.
5. For `B_n = A(A_(n-1))`, `|Φ^+| = n(n-1)/2`, so
   `B_n -> GL_(n(n-1))(Z[t^{±1}])` is injective. Types `D` and `E` work the
   same way with `N = |Φ^+|`. ∎

Scope. The faithfulness is Cohen–Wales's theorem, read in the source above.
The proof of that theorem (§4) was not re-derived here.
