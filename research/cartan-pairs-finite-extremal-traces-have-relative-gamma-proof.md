---
rg: 2
id: cartan-pairs-finite-extremal-traces-have-relative-gamma-proof
kind: route
title: Balance hyperfinite orbit-invariant partitions by Lyapunov against the finitely many trace measures
target: cartan-pairs-finite-extremal-traces-have-relative-gamma
requires: []
artifacts:
  - research/artifacts/cartan-finite-extremal-relative-gamma-2026-09-16.md
---

The full proof is in the artifact. The steps are:

1. **Finitely many traces.** `T(A) = conv{tau_1, ..., tau_m}`. So the
   uniform 2-norm is the maximum over the `tau_j`, and every limit trace is
   an ultralimit of convex combinations of the `tau_j`.
2. **Commutator formula.** Kumjian's relation `n^* d n = (d ∘ α_n) n^*n`
   gives `[n, f]^*[n, f] = (f − f ∘ α_n)^2 n^*n` for normalizers `n` and
   self-adjoint `f ∈ D`. Tracial central sequences from `D` are therefore
   controlled by the measures `μ_j = tau_j|_D` alone; traces need not
   factor through `E`.
3. **The measures `μ_j`.** The trace property makes each `μ_j` invariant
   under every `α_n`. Each `μ_j` has no atoms: an atom forces a finite
   closed invariant orbit, and then a regular representation of the
   Weyl twisted groupoid has a proper nonzero kernel, contradicting
   simplicity.
4. **Hyperfinite orbit relation.** `A` is nuclear, so the Weyl groupoid
   is amenable (Takeishi, Theorem 5.4, as quoted in Barlak–Li,
   arXiv:1511.02697v3). Pushing continuous approximate invariant means
   along the source map gives a Borel Reiter sequence for the orbit
   relation `R`. By Connes–Feldman–Weiss, `R` is `μ`-hyperfinite for
   `μ = avg μ_j`.
5. **Balanced partitions.** Pick a finite subrelation `R_l` that
   captures all finitely many test normalizers off a small set. On a
   Borel transversal of `R_l`, apply Lyapunov's convexity theorem to the
   nonatomic vector measure `(μ_j([·]_{R_l}))_j`. This yields
   `R_l`-invariant Borel sets `B_1, ..., B_k` with `μ_j(B_i) = 1/k`,
   almost invariant under the test normalizers.
6. **Continuous approximation.** Urysohn functions give `f_i ∈ D` with
   `Σ f_i = 1` that approximate the `1_{B_i}` in `L^1(μ_j)`. The formula
   in step 2 bounds the commutator 2-norms.
7. **Ultrapower assembly.** A diagonal sequence gives projections
   `q_i ∈ κ(D^U) ∩ A'` summing to `1`. For each extremal `tau_j`, the
   functional `a ↦ lim tau_j(q_i a)` is tracial and dominated by `tau_j`,
   hence equal to `tau_j/k`. This gives KLTV (3.3) for all `a ∈ A`.

Imported ingredients, all standard:
- Renault's reconstruction theorem and Kumjian's normalizer
  homeomorphisms;
- Takeishi's nuclearity-implies-amenability theorem;
- Anantharaman-Delaroche–Renault approximate invariant means;
- Connes–Feldman–Weiss;
- Lusin–Novikov;
- Lyapunov's convexity theorem.

The artifact records which citations were verified and which carry
unverified theorem numbers. The referee checked F1–F3 against the primary
sources on 2026-09-16: Renault, arXiv:0803.2284v1, Proposition 4.6,
Proposition 4.7(ii) and Theorem 5.6; Takeishi, arXiv:1301.6883v1, Theorems
5.3 and 5.4. The remaining imports are textbook theorems: approximately
invariant means for amenable étale groupoids, Connes–Feldman–Weiss in
Reiter form, Lusin–Novikov and Lyapunov.
