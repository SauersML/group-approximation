---
rg: 2
id: nonunit-component-root-mass-is-log-scale-folner
kind: claim
title: Under vertex rounding, all non-unit root mass beyond depth one, pure or mixed, is at most the transport defect times the number of d-adic scales
distinct_from:
  pure-nonunit-root-mass-is-log-scale-folner: that measures the depth of the whole character, which is infinite on mixed characters, so it bounds only pure non-unit mass; this measures the depth of the non-unit component alone, which is finite for every character, and bounds pure and mixed non-unit mass at once.
  compressor-transport-exactifies-under-vertex-rounding: that is the total-variation invariance of root spectra under the compressor; this applies it to the non-unit-component depth filtration, after showing the compressor transport acts componentwise.
  nonunit-projection-bounded-by-root-spectral-mass: that bounds the non-unit projection by the root mass nontrivial on the non-unit factor; this bounds that mass except for its shallow part.
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open rounding statement; this removes mixed constituents as a separate regime, leaving the slow-rate spread and shallow non-unit mass.
---

**ESTABLISHED.** Take the setting and hypotheses of
`compressor-transport-exactifies-under-vertex-rounding`, with `η_n = 4δ_n^2/κ^2`,
`z = x_1 ⋯ x_d`, and `μ_n` the normalized spectral measure of `f -> π_n(e_12(f))`.

**Components.**
- Let `χ` be a character of `(R_+, +)` whose kernel contains a finite-index ideal `I`. It factors through
  `B = R_+/I = A_u × A_nu`, the split into unit-type and non-unit local factors.
- Put `χ_u(f) = χ(e_u f)` and `χ_nu(f) = χ(e_nu f)`, with `e_u, e_nu` the idempotents. The components do not
  depend on the choice of `I`.
- Define

  ```text
  depth_nu(χ) = min{k >= 0 : χ_nu is trivial on z^k R_+}.
  ```

  It is finite for every such `χ`, and `depth_nu(χ) = 0` iff `χ_nu = 1`.

1. **Componentwise transport.** For `D_A χ = χ ∘ φ_A`, the components transport separately:
   `(D_A χ)_u = χ_u ∘ φ_A` and `(D_A χ)_nu = χ_nu ∘ φ_A`. Moreover `χ_u ∘ φ_A ≠ 1` iff `χ_u ≠ 1`.
2. **Contraction.** `depth_nu(D_A χ) <= ⌈depth_nu(χ)/d⌉`.
3. **Per-scale bound.** `μ_n(d^j < depth_nu <= d^(j+1)) <= η_n` for every `j >= 0`.
4. **Total bound.** `μ_n(depth_nu > 1) <= η_n · (1 + log_d(r(r-1)n'))`.
5. **Non-unit projection.** With `P_n` as in
   `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`,

   ```text
   τ(1 - P_n)  <=  r(r-1) · [ μ_n(depth_nu = 1) + η_n (1 + log_d(r(r-1)n')) ].
   ```

**Reading.**
- **Mixed constituents are not a separate regime.** Constituents nontrivial on both factors are regime (iii) of
  `theorem-e-vertex-rounds-to-unit-type-representations`. The depth of the non-unit component sees
  them exactly as it sees pure non-unit ones. The unit component rides along and is invisible to the
  filtration.
- **No entanglement.** `St_r(A_u × A_nu) = St_r(A_u) × St_r(A_nu)`, so a mixed irreducible constituent is a
  tensor product `τ_u ⊗ τ_nu` with both factors nontrivial. There is nothing to exploit, and nothing that
  escapes the filtration.
- **What survives** of the non-unit mass:
  - (i) mass spread over at least `1/η_n` d-adic scales, possible only when `δ_n^2 log n` does not tend to 0;
  - (ii) shallow mass `μ_n(depth_nu = 1)`: characters whose non-unit component is nontrivial but
    trivial on `zR_+`. This regime now contains mixed characters as well as pure ones.

No root is affected. Derivation: `nonunit-component-root-mass-folner-proof`.
