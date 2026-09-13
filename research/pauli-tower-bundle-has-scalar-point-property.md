---
rg: 2
id: pauli-tower-bundle-has-scalar-point-property
kind: claim
title: The uniform tracial completion of the Pauli tower is an R-fibre W*-bundle in which every self-adjoint element is scalar at some point
distinct_from:
  trivial-r-fibre-bundles-compare-equal-trace-projections: that certifies nontriviality by a comparison gap between existing projections; this certifies it by an existence gap, since no nowhere-scalar self-adjoint element exists at all.
  nontrivial-w-star-bundle-with-r-fibres-exists: that is the existence question; this is an explicit bundle carrying an invariant that no trivial bundle has.
  pauli-tower-sections-are-somewhere-scalar: that is the finite-stage topological theorem; this passes it to the inductive limit and its uniform tracial completion.
artifacts:
  - research/artifacts/tw-pauli-tower-scalar-point-bundle-2026-09-13.md
---

**Statement (unreviewed).** With `B_k → Y_k` as in `pauli-tower-sections-are-somewhere-scalar`,
let `A = lim_m C(Π_{k≤m} Y_k, ⊠_{k≤m} B_k)` with maps `a ↦ a ⊗ 1`, and `X̂ = Π_k Y_k`. Let `M` be
the uniform tracial completion of `A`.
1. `A` is a unital separable nuclear `C(X̂)`-algebra, all fibres `M_{2^∞}`, `T(A) = Prob(X̂)`. So `M`
   is a strictly separable continuous W*-bundle over the compact metrizable space `X̂` with every
   fibre `R`.
2. **Scalar point property.** Every self-adjoint `x ∈ M` has `λ ∈ X̂` with `π_λ(x) ∈ C·1`.
3. `M` is not isomorphic to `C_σ(X̂, R)`.

**Proof sketch.**
- **Traces.** Traces of `C(Z_m, B)` are integrals of the fibre trace against probability measures,
  and `T(A)` is their inverse limit. So `∂_e T(A) = X̂` is closed, and
  `closed-extreme-trace-sets-give-r-fibre-w-star-bundles` gives the bundle.
- **Variance.** `Var_λ(y) = E(y²)(λ) − E(y)(λ)²` vanishes exactly where `π_λ(y)` is scalar.
  `min_λ Var_λ` is `4C`-Lipschitz in `‖·‖_{2,u}` on self-adjoint elements of norm `≤ C`.
- **Limit.** It is `0` on every finite stage, by the finite-stage theorem with `n = 0`. Bounded
  self-adjoint approximation from `∪_m A_m` passes this to `M`.
- **Nontriviality.** In `C_σ(X̂, R)` a constant projection of trace `1/2` has variance `1/4`
  everywhere, and W*-bundle isomorphisms preserve `E`.

**Consequences (unreviewed).**
- **Question 3.14.** Route `nontrivial-w-star-bundle-via-pauli-tower` into
  `nontrivial-w-star-bundle-with-r-fibres-exists`.
- **No uniform `M_2`.** `pauli-tower-bundle-has-no-uniform-order-zero-m2` refutes
  `r-fibre-w-star-bundles-divide-the-unit-uniformly`.
  - Sharper form: of two orthogonal positive elements, one vanishes in some fibre.
  - So every order zero `M_N → M` (`N ≥ 2`) vanishes in some fibre (part 2, Theorem C).
- **No Z-stability, no projections.** `A` is not Z-stable, and it has no projections other than
  `0` and `1`.
- **Consistency with the localization theorems.** `X̂` contains a Hilbert cube, and every point has
  only infinite-dimensional neighbourhoods. This is consistent with Ozawa's Corollary 16, with
  `r-fibre-w-star-bundle-sigma-finite-dim-base-is-trivial`, and with
  `bauer-gamma-failure-localizes-to-infinite-dim-point`. The bundle is not locally trivial.
- **The gap sits at the unit only.** `e_{11} ⊗ 1 ∈ M_2(M)` has constant trace `1/2`.
- **Not McDuff, but McDuff after one tensor factor.**
  - By Ozawa's Theorem 15 (`r-fibre-bundle-triviality-iff-uniform-central-halving`), trivial
    strictly separable R-fibre bundles are exactly the McDuff ones, so `M` is not McDuff.
  - `M ⊗̄ R` over `X̂` is trivial: `1 ⊗ e_j`, with `e_j ∈ R` asymptotically central projections of
    trace `1/2`, is a uniformly central halving sequence on the dense algebraic tensor product.
  - So Question 3.14 is witnessed by a non-McDuff bundle whose McDuffication is trivial.
