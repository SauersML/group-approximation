---
rg: 2
id: unit-type-vertex-rounding-forces-compressor-commutant-rigidity
kind: claim
title: Under vertex rounding, the commutant excess of the Theorem E compression is carried by non-unit congruence mass
distinct_from:
  vertex-rounding-reduces-ccr-to-commutant-excess: that identifies (CCR) with vanishing of the finite excess eps_n under (H1); this bounds eps_n by the trace of the non-unit constituents of the rounded vertex representations, using the congruence structure of the explicit Theorem E vertex.
  fd-invisibility-of-compression: that shows rho(Lambda) = rho(E) for genuine representations of the actor, where every variable is a unit; this treats genuine representations of the polynomial vertex alone, where non-unit congruence factors exist and the collapse can fail on them.
  char-p-root-torsion-collapse: that derives congruence factorization for representations of the actor G; this runs the same root-torsion argument over the polynomial ring, splits the finite quotient into unit-type and non-unit local factors, and proves an excess estimate.
  ccr-for-coordinate-collapsing-models: that assumes image collapse in genuine coordinates of G; this works in the (H1) regime, where only the vertex is rounded, and proves the collapse exactly on the unit-type part.
  hs-normalization-needs-coarse-actor-scale-pinning: that closes (CCR) from (H1) together with the coarse actor gap (H2'); this closes (CCR) from (H1) together with an arithmetic condition, vanishing non-unit mass, with no actor gap and no median step.
artifacts:
  - research/artifacts/nh-h1-rounding-2026-09-12.md
---

**ESTABLISHED.** Let `R_+ = F_q[x_1..x_d]` and `L = F_q[x^(±1)]`, with `r, d >= 3`. Let
`Γ = EL_r(R_+) < G = EL_r(L) ⋊ SL_d(Z)` be the explicit Theorem E pair, `A ∈ SL_d(Z)` a
nonnegative compressor, and `Λ = AΓA^(-1) = EL_r(S)` with `S = F_q[x^(A e_1)..x^(A e_d)]`.
Let `σ : G -> U(prod_U M_n)` be trace-preserving and satisfy (H1) of
`hs-normalization-needs-coarse-actor-scale-pinning`, with rounding representations
`π_n : Γ -> U(n')`.

1. **Finite images.** Each `π_n` factors through a finite Steinberg group `St_r(R_+/I_n)` for an
   ideal `I_n` of finite index. The proof is the root-torsion argument: root subgroups have
   exponent `p`, and the Steinberg commutator relation makes the kernel ideal-closed.
2. **Unit-type collapse.** Write `R_+/I_n = A_u × A_nu`, where `A_u` collects the local factors
   in which every `x_i` is a unit. Let `P_n` be the central projection of `π_n(Γ)''` onto the
   constituents that are trivial on `St_r(A_nu)`. Then `π_n(Γ)P_n = π_n(Λ)P_n`, because the
   image of `S` in `A_u` is all of `A_u`.
3. **Excess bound.** With `eps_n` as in `vertex-rounding-reduces-ccr-to-commutant-excess`,

   ```text
   eps_n <= 4 tau(1 - P_n)^(1/2).
   ```

4. **Normalization.** If `tau(1 - P_n) -> 0` along `U` then (CCR) holds for every nonnegative
   strict compressor. Since `G = <Γ, e_ij(1)>`, `σ(G)` normalizes `σ(Γ)' ∩ prod_U M_n`.

**Reading.**
- (H1) with unit-type rounding suffices. The coarse actor gap (H2') and the median step are not
  needed.
- Excess can live only on non-unit congruence factors, where some `x_i` is nilpotent.
- Genuine `G`-models restrict to unit-type factorizations, so for them `P_n = 1`.
- The open input is `theorem-e-vertex-rounds-to-unit-type-representations`.

No root is affected. Derivation: `unit-type-vertex-rounding-ccr-proof`.
