---
rg: 2
id: relator-adjunctions-grow-degree-two-cohomology
kind: claim
title: Adding aspherical relators to a Kazhdan two-complex group raises b_2 and b_2^(2) by the number of relators
distinct_from:
  kazhdan-two-complex-b2-is-euler-characteristic-minus-one: that computes b_2 of one Kazhdan group from a nonpositively curved 2-complex; this tracks how b_2 and b_2^(2) change when finitely many relators are attached aspherically, as in small cancellation quotients
  ghb7-kernel-blocks-degree-two-newton-stability: that blocks the degree-two Newton scheme for the single group H; this shows the same obstruction for every aspherical relator quotient, and that it strictly grows with the number of relators
  aspherical-adjunction-has-zero-schur-kernel: that shows an aspherical relative 2-complex keeps every Schur multiplier class; this counts the new degree-two classes, rational and L2, that each attached relator adds
artifacts:
  - research/artifacts/solve-sc-hyperbolic-kazhdan-2026-09-13.md
---

**ESTABLISHED** by [[relator-adjunctions-degree-two-growth-proof]].

Let `Γ` be an infinite group with property (T) and a finite 2-dimensional
`K(Γ,1)` complex `X`. Let `R` be a finite nonempty set of closed edge loops in `X`,
attach one 2-cell along each, put `Y = X ∪_R e²` and `Q = π_1(Y) = Γ/⟨⟨R⟩⟩`.
Suppose `Y` is aspherical. Then:

1. **Rational.** `b_2(Q;Q) = b_2(Γ;Q) + |R|`.
2. **L2.** `Q` is infinite, and
   `b_2^(2)(Q) = χ(Y) = b_2(Γ;Q) + 1 + |R|`, with `b_k^(2)(Q) = 0` for `k ≠ 2`.
   In particular `H²(Q; ℓ²Q) ≠ 0`.
3. **Ad-modules.** Suppose moreover `Q` is torsion-free, word-hyperbolic and
   non-elementary, and `σ_n : Q → U(d_n)` is a separating asymptotic representation.
   Put `π = Ad(σ ⊗ σ)` on `L²(M)`, where `M` is the tracial ultraproduct of the
   `M_{d_n²}`. Then `H²(Q; π) ≠ 0` on the trivial summand, and also on a traceless
   summand containing `ℓ²(Q) ⊗ ℓ²(N)`.

**Consequence for stability proofs.** Attaching relators aspherically never supplies
degree-two cohomology vanishing. It adds exactly `|R|` rational classes and `|R|`
units of `b_2^(2)`, so the obstruction of `ghb7-kernel-blocks-degree-two-newton-stability`
only grows. A small-cancellation route to `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`
must therefore use a mechanism other than degree-two vanishing (De Chiffre–Glebsky–Lubotzky–Thom
iteration, `hs-stability-from-bounded-degree-two-primitives`).

The `b_2 >= 1` clause of `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` is
preserved automatically under such quotients: `b_2(Q;Q) >= |R| >= 1`.

**Scope.** Asphericity of `Y` is a hypothesis. It is not claimed here for any
small-cancellation condition over a hyperbolic group; that input was not
source-checked in this lane (see the artifact).
