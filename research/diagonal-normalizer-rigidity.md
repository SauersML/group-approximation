---
rg: 2
id: diagonal-normalizer-rigidity
kind: claim
title: Approximate normalizers of a full diagonal masa are monomial
invalidates: [masa-normalizing-tracial-action]
distinct_from:
  coordinate-action-not-sofic: that is a fact about the Kun–Thom coset action, imported by citation; this is a metric rigidity theorem about single unitaries, proved here, and it is what makes the citation bite against normalizers rather than only against permutations
  finite-quotient-blindness: that says exact finite quotients normalize Γ's image; this says approximate unitary normalizers of a full masa are close to monomials, a statement about ‖·‖₂ geometry with no group homomorphism in it
artifacts:
  - notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

For `u ∈ U(N)` let

```text
def_D(u) = sup{ ‖u f u* − E_(D_N)(u f u*)‖₂ : f = f* ∈ D_N, ‖f‖ ≤ 1 }
```

measure how far `u` is from normalizing the **full** diagonal masa `D_N`,
in normalized Hilbert–Schmidt norm.

1. **Rigidity.** `def_D(u) ≤ δ` implies `‖u − w‖₂ ≤ 3√δ` for some monomial
   unitary `w = P_σ d`. (Proof: `A_ij = |u_ij|²` is doubly stochastic and the
   defect equals `sup(‖f‖₂² − ‖Af‖₂²)`; random signs force
   `E_i[max_j A_ij] ≥ 1 − δ²`.)
2. **Ultraproduct form.** `N(D_𝒰) = 𝒮_𝒰 ⋉ U(D_𝒰)`, with unique factorization.
3. **Transfer.** `‖·‖₂`-multiplicativity of `φ : Γ → U(N)` passes to Hamming
   multiplicativity of the extracted permutations `π(g)`, with defect
   `(ε + 9√δ)²/2`.
4. **Consequence (permutations are not needed in Păunescu's definition).**
   For `G` sofic, a trace-preserving embedding
   `Θ : L^∞(X) ⋊ G → ∏_𝒰 M_(d_n)` with `Θ(L^∞(X)) ⊆ D_𝒰` and merely
   `Θ(u_g) ∈ N(D_𝒰)` already makes the action sofic in the sense of
   Kun–Thom Definition 2.2. The diagonal phases are removed by untwisting
   (`c_g ∈ U(D_𝒰)` commutes with `Θ(L^∞(X))`, so the permutation part alone
   implements the action) and the residual trace defect by tensoring with a
   free sofic representation of `G`.

Clause 1 is sharp in its hypothesis: it needs the **full** masa. If only a
coarse subalgebra must be respected, the Fourier-block unitary
`⊕_j F_(m_n)` centralizes it while sitting at distance `√2` from every
monomial.
