---
rg: 2
id: pure-braided-thompson-group-is-residually-nilpotent-proof
kind: route
title: P_br is residually nilpotent via strand-deletion retractions and the Artin representation
target: pure-braided-thompson-group-is-residually-nilpotent
requires: []
artifacts:
  - research/artifacts/zp-braided-v-hopfian-2026-09-13.md
---

1. **Retractions.** Cloning strand `k` of a pure braid (bifurcating it into two
   parallel strands) is an injective homomorphism `kappa_k: PB_n -> PB_{n+1}`.
   Deleting the clone `k+1` is a homomorphism `delta: PB_{n+1} -> PB_n` with
   `delta ∘ kappa_k = id`. Iterating, for trees `T <= T'` the inclusion
   `PB_T -> PB_{T'}` in `P_br` has a left-inverse homomorphism `r`.
2. **Stages.** Homomorphisms preserve lower central series terms. If `x` lies in
   `PB_T ∩ gamma_c(PB_{T'})`, then `x = r(x)` lies in `gamma_c(PB_T)`. `P_br` is the
   directed union of the `PB_{T'}`, and every commutator involves finitely many
   elements, so `gamma_c(P_br) = ∪_{T'} gamma_c(PB_{T'})`. This gives
   `gamma_c(P_br) ∩ PB_T = gamma_c(PB_T)`.
3. **Pure braid groups.** Artin's representation `PB_n -> Aut(F_n)` is faithful, and a
   pure braid sends each generator `x_i` to a conjugate of `x_i`. So its image lies in
   `IA_n = A_1`, where `A_c = ker(Aut(F_n) -> Aut(F_n/gamma_{c+1}F_n))`.
   - Andreadakis (1965) gives `[A_1, A_c] <= A_{c+1}`, so by induction
     `gamma_c(IA_n) <= A_c`.
   - Free groups are residually nilpotent (Magnus), so `∩_c A_c = 1`.
   - Hence `∩_c gamma_c(PB_n) = 1`.
4. **Conclusion.** An element of `∩_c gamma_c(P_br)` lies in some `PB_T`. By step 2 it
   lies in `∩_c gamma_c(PB_T) = 1`.
   - The embedding of graded pieces follows from step 2 at `c` and `c+1`:
     `gamma_c(PB_T) ∩ gamma_{c+1}(P_br) = gamma_{c+1}(PB_T)`.

**Credit and related work.**
- Residual nilpotence of `PB_n` is classical and is commonly credited to Falk–Randell. That
  source was not re-read here; step 3 is a self-contained derivation.
- Burillo–González-Meneses, *Bi-orderings on pure braided Thompson's groups*
  (arXiv:math/0608646v1), treat the same direct limit `PBV = P_br`. Read from the PDF:
  - Lemma 3.1 shows that doubling a strand preserves the Kim–Rolfsen bi-order of the pure
    braid group, through the lower central series of `F_n` and the Magnus expansion.
  - Corollary 3.2: "The group PBV is bi-orderable."
  - Theorem 3.3: "The group BF is bi-orderable."
  They do not state residual nilpotence of `P_br`, but their argument that cloning is
  compatible with the lower-central-series structure is closely related to step 2 and step 3,
  and should be credited alongside this node.
