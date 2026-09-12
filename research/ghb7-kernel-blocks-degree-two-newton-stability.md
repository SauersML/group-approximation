---
rg: 2
id: ghb7-kernel-blocks-degree-two-newton-stability
kind: claim
title: The GHB_2(7) congruence kernel has nonzero degree-two cohomology on the Ad-modules of its tensor-squared microstates
distinct_from:
  bounded-degree-two-primitives-for-higher-rank-lattices: that asks for operator-bounded primitives of 2-cocycles that are already coboundaries, for SL_N(Z); this shows that for the GHB_2(7) kernel the cocycles need not be coboundaries at all, on the trivial summand and on a regular summand of the Ad-module
  flat-calibrations-refute-bounded-degree-two-primitives: that refutes operator-norm control for lattices containing flats; this is a vanishing failure in degree two driven by a positive second L2-Betti number, in a hyperbolic group with no flats
  hs-stability-forces-nonhyperlinear-central-extension: that turns stability plus a central extension into non-hyperlinearity through rigidity; this records that degree-two cohomology vanishing cannot be the source of that stability for this candidate
---

**ESTABLISHED** by [[ghb7-kernel-degree-two-newton-block-proof]].

Let `H` be the congruence kernel of `G_{HB_2}(7)` from
`ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`.

1. **Trivial summand.** `H^2(H; C) ≠ 0`, since `b_2(H;Q) >= 1380`.
2. **Regular summand.** Suppose `H` is hyperlinear, with a separating asymptotic
   representation `σ_n : H → U(d_n)`. Put `ρ_n = σ_n ⊗ σ_n`, let `M` be the tracial
   ultraproduct of the `M_{d_n^2}`, and let `π = Ad ρ` act on `L²(M)`. Then
   `L²(M) ⊖ C` contains a copy of `ℓ²(H) ⊗ ℓ²(N)`, and `H^2(H; π) ≠ 0` on that
   summand.
3. **Consequence for stability proofs.** The degree-two existence scheme for flexible
   HS stability solves `δy = c` for the relator-defect 2-cocycle `c` in `L²(M)` under
   `Ad`. This is the De Chiffre–Glebsky–Lubotzky–Thom iteration and the route
   `hs-stability-from-bounded-degree-two-primitives`. For `H` that scheme has no
   vanishing input. Its hypothesis `H^2(H; π) = 0` fails on the trivial summand, and,
   whenever `H` is hyperlinear, also on a traceless regular summand.

   So a proof that `H` is flexibly HS stable must do one of two things:
   - show that the defect cocycles of every asymptotic representation avoid these
     nonzero classes;
   - or use a mechanism other than degree-two cohomology vanishing.

**Scope.** This is a statement about a proof method, not a proof that `H` is unstable:
the specific defect cocycles may still be coboundaries.

**Degree one is not the obstruction.** Property (T) gives uniform `H^1` vanishing for
all unitary coefficients. That input yields rigidity (uniqueness of rounding, property
(T;FD)), which is how `hs-stability-forces-nonhyperlinear-central-extension` consumes
it. It does not yield the existence of nearby genuine representations.

**The non-hyperlinear case.** If `H` is not hyperlinear, `H` already answers
`non-hyperlinear-group`. So the hypothesis of item 2 is the only case in which
stability of `H` matters.
