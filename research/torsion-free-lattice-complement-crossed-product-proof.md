---
rg: 2
id: torsion-free-lattice-complement-crossed-product-proof
kind: route
title: Implement the coupling cocycle of the lattice on the compact open corner by finitely many translations of the complement
target: torsion-free-lattice-embeds-in-complement-crossed-product
requires: []
artifacts:
  - research/artifacts/fournier-facio-simple-factor-corner-2026-09-16.md
---

Artifact Section 1.1, Steps 1–8. Notation as in the target. `v_λ` are the canonical
unitaries, with `v_λ 1_B v_λ^* = 1_{λB}`.

1. **Corner.** `k ↦ kS` is injective on `K`, because `K ∩ S = 1`, and continuous. So it is a
   homeomorphism onto the clopen set `A = KS/S`. `μ` has full support, so `τ(p) = μ(A) > 0`.
2. **Cocycle.** The factorization `h = λ(h)κ(h)` is unique because `Λ ∩ K = 1`, and `λ(·)`
   is locally constant because `H = ⊔_λ λK` is an open partition. From `kst = λ(k,s) κ(k,s) t`:

   ```text
   λ(k, st) = λ(k,s) λ(κ(k,s), t),     κ(k, st) = κ(κ(k,s), t).
   ```

3. **Pieces.** For fixed `s`, the sets `A_{s,λ}` are clopen and partition the compact set `A`.
   So finitely many are nonempty. If `kS ∈ A_{s,λ}`, then `λ^{-1}kS = κ(k,s)S ∈ A`, and by
   step 2, `λ^{-1}A_{s,λ} = A_{s^{-1},λ^{-1}}`. So `u_s ∈ pMp`, and `u_1 = p`.
4. **Products.** `(v_{ν^{-1}} 1_C)(v_{λ^{-1}} 1_B) = v_{(λν)^{-1}} 1_{B ∩ λC}`. So
   `u_s u_t = Σ v_{(λν)^{-1}} 1_{A_{t,λ} ∩ λA_{s,ν}}`, and
   `A_{t,λ} ∩ λA_{s,ν} = {kS : λ(k,t) = λ, λ(κ(k,t), s) = ν}`. By step 2 these sets, over
   `λν = μ_0`, partition `A_{ts,μ_0}`. Hence `u_s u_t = u_{ts}`.
5. **Adjoints.** `u_s^* = Σ_λ v_λ 1_{λ^{-1}A_{s,λ}} = u_{s^{-1}}`. So each `u_s` is a unitary of
   `pMp`, and `w_s = u_{s^{-1}}` is a homomorphism.
6. **Trace.** `τ(u_s) = μ(A_{s,1})`. If `k ∈ K` and `ks ∈ K`, then `s ∈ K ∩ S = 1`. So
   `τ(u_s) = δ_{s,1} τ(p)`.
7. **Group factor.** A trace-preserving unital *-homomorphism `C[S] → (pMp, τ(p)^{-1}τ)`
   extends to a normal trace-preserving embedding of `L(S)`, because the GNS completions agree.
8. **Connes embeddability.** A corner `pMp` of a Connes-embeddable `M` is Connes-embeddable, and
   so is its von Neumann subalgebra `L(S)`. These are standard permanence facts, used the same
   way in `sp4-finite-index-scalar-data-hyperlinear-covers-proof`. ∎
