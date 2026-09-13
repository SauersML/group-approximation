---
rg: 2
id: sl3z-cocompact-wc-iff-weak-limit-of-congruence-quotients-proof
kind: route
title: Induce from SL3(Z) to SL3(R) and project to the second factor; conversely restrict and use Benoist-Quint equidistribution of Hecke orbits
target: sl3z-cocompact-wc-iff-weak-limit-of-congruence-quotients
requires:
  - benoist-quint-zariski-dense-invariant-measures-are-haar
---

Notation: `G = SL_3(R)`, `Γ = SL_3(Z)`, `X = G/Λ`, and `≺` denotes weak containment in mixtures.

**Lemma A (induction).** Let `Γ <= G` be a lattice with a Borel fundamental domain `F`, `G = ⊔_(γ∈Γ) Fγ`, such
that every compact set meets finitely many translates `Fγ`. A Siegel domain works for `SL_3(Z)`
(recalled). If `a ≺ b` for `Γ`-actions, then `Ind_Γ^G a ≺ Ind_Γ^G b`.

*Proof.* Model `Ind a` as `F × X_a` with normalized `m_F × μ` and `h·(f,x) = (f', c(h,f)x)`, where `hf = f'c(h,f)`
with `f' ∈ F` and `c(h,f) ∈ Γ`. Fix sets `A_1..A_n`, a compact `K ⊆ G` and `ε > 0`. Choose a compact
`F_R ⊆ F` with `m_F(F ∖ F_R) < ε`, a finite Borel partition `C_1..C_p` of `F_R`, and Borel `B_(ik) ⊆ X_a` such
that `A_i` is within `ε` of `∪_k C_k × B_(ik)`. The set `E = {c(h,f) : h ∈ K, f ∈ F_R}` is finite, because
`KF_R` is compact. For `h ∈ K`,

```text
(m_F×μ)( h(C_k × B_(ik)) ∩ (C_l × B_(jl)) ) = Σ_(γ ∈ E) m_F({f ∈ C_k : c(h,f) = γ, f' ∈ C_l}) · μ(γB_(ik) ∩ B_(jl)).
```

The coefficients do not depend on the action, and they sum to at most `m_F(C_k)`. Choose `B'_(ik)` in `b`
(or in a mixture) reproducing the finitely many numbers `μ(γB_(ik) ∩ B_(jl))`, `γ ∈ E ∪ {1}`, within
`ε/p^2`. Then `A'_i = ∪_k C_k × B'_(ik)` reproduces every statistic within `O(ε)`, uniformly in `h ∈ K`. A
mixture induces to the mixture of the induced actions. ∎

**Lemma B (restriction).** If `a ≺ b` for `G`-actions, then `Res_Γ a ≺ Res_Γ b`. A finite subset of `Γ` is compact. ∎

**Lemma C (Hecke).** For every finite-index `Γ' <= Γ`, `Γ ↷ (G/Γ', Haar)` is weakly contained in finite actions.

*Proof.* `Comm_G(Γ') ⊇ SL_3(Q)` has infinite index over `Γ'`. So the points `cΓ'`, `c ∈ SL_3(Q)`, lie on
infinitely many finite `Γ`-orbits, by the counting in Instance 1 of
`hecke-orbits-make-lattice-quotient-actions-sofic-proof`. Taking distinct orbits `X_n`, Corollaire
1.2(c) of `benoist-quint-zariski-dense-invariant-measures-are-haar` makes their normalized counting
measures converge to Haar measure on `C_c(G/Γ')`. For Haar-continuity sets `A_i` and finite `S ⊆ Γ`, the
sets `sA_i ∩ A_j` are continuity sets, so the finite actions `Γ ↷ X_n`, with partitions `A_i ∩ X_n`,
reproduce the statistics in the limit. Continuity sets generate the measure algebra, which suffices
for weak containment. ∎

**(1) ⇒ (2).** Every finite `Γ`-set is a union of orbits `Γ/Γ_v`, and `Ind(Γ/Γ_v) = G/Γ_v`. So `Ind` of a
mixture of finite actions is a mixture of actions `G ↷ G/Γ'`. By Lemma A, `Ind X ≺` such mixtures. Now
`Ind X = G ×_Γ X ≅ G/Γ × X`, with `G` acting diagonally, through `[g,x] ↦ (gΓ, gx)`. Projection to `X` is a
factor map, and factors of weakly contained actions are weakly contained. ∎

**(2) ⇒ (1).** By Lemma B, `Γ ↷ X ≺` mixtures of `Γ ↷ G/Γ'`. Each is `≺` finite actions by Lemma C, and a
mixture of such is `≺` mixtures of finite actions. Weak containment is transitive. ∎

**Congruence form.** Every finite-index `Γ'` contains some `Γ(N)` (congruence subgroup property), and
`G/Γ(N) → G/Γ'` is a factor. So the mixtures in (2) may be taken over `{G/Γ(N)}`.
