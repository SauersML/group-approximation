---
rg: 2
id: howe-moore-lattice-nonsofic-action-transfers-to-mixing-proof
kind: route
title: Induce the seed to the Howe-Moore envelope, identify the index-one self-coupling as an orbit equivalence, and read nonsoficity off the Gamma-backslash-H factor
target: howe-moore-lattice-nonsofic-action-transfers-to-mixing
requires:
  - paunescu-orbit-equivalent-free-actions-share-soficity
  - sofic-action-class-closed-under-commensurability
  - paunescu-sofic-action-class-permanence
  - sofic-action-with-sofic-ergodic-components-is-sofic
artifacts:
  - research/artifacts/nonsofic-action-mixing-transfer-2026-09-12.md
  - research/artifacts/nonsofic-action-mixing-transfer-part2-2026-09-12.md
---

Full proof: part 2 artifact, Section 5 (Steps 1-7). Lemma EQ is in part 1, Section 4.

1. **Seed.** `Γ` is nonamenable (Păunescu Proposition 3.4), hence infinite. `Z' = Z × {0,1}^Γ` is
   essentially free and nonsofic, because `Z` is a factor (Lemma A of
   `sofic-action-class-commensurability-proof`). It is ergodic: on `L²(Z) ⊗ L²_0(B)` the coefficients
   vanish at infinity, because the Bernoulli shift is mixing, and `L²_0(Z)` has no invariant vectors.
2. **Coupling.** `H` is unimodular. On `Ω = H × Z'` let `γ·(h,z) = (γh, z)` and
   `γ∗(h,z) = (hγ^(−1), γz)`. The fundamental domains `D × Z'` and `D' × Z'` both have measure
   `covol(Γ)`. The quotients are `W = Ω/Γ_r = H ×_Γ Z'` and `V = Γ_ℓ\Ω = Γ\H × Z'`.
3. **`V` is free and nonsofic.** Its stabilizers lie in the stabilizers of `Z'`, and `(Γh,z) ↦ z` is a
   factor map onto `Z'`; apply Lemma A.
4. **`W` is free.** `γ[h,z] = [h,z]` forces `(γh,z) = (hδ^(−1), δz)`, so `δ = 1` off a null set, and then
   `γ = 1`.
5. **`W` is mixing.** `H ↷ W` is ergodic: by Fubini an invariant set is `H × E_0` with `E_0` invariant
   in `Z'`. Howe--Moore makes the Koopman coefficients on `L²_0(W)` `C_0`, and a discrete `Γ` meets each
   compact set finitely.
6. **Orbit equivalence.** Both orbit relations are restrictions of the `Γ × Γ` orbit relation `R` on
   `Ω` to the two fundamental domains. `R` restricted to their union `X` is ergodic, since an invariant
   set descends to a `Γ`-invariant set of the mixing space `W`. Lemma EQ (in an ergodic countable
   p.m.p. relation, sets of equal measure are equivalent by a partial isomorphism, proved by greedy
   exhaustion along Feldman--Moore generators) gives `φ ∈ [[R]]` from one domain onto the other. `φ`
   is an orbit equivalence of the free actions `Γ ↷ W` and `Γ ↷ V`.
7. **Conclusion.** Păunescu Theorem 1.5: were `W` sofic, `V` would be sofic.

**Dichotomy.** If `Γ ∉ 𝒮`, `sofic-action-with-sofic-ergodic-components-is-sofic` supplies an ergodic
nonsofic seed.
