import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendBoundedStatement
import Mathlib.Analysis.Normed.Operator.Banach
import GroupApproximation.Meta.AxiomGuard

/-!
# Polar unitary, lane `nm-tww-17b`: adjointable maps between complete modules are bounded

`adjointableBounded : AdjointableBoundedStatement B`, proved from Mathlib's closed graph theorem
`ContinuousLinearMap.ofSeqClosedGraph`.

Route.
* The carrier of `E` is a normed space (`CStarModule.toNormedAddCommGroup` plus
  `CStarModule.norm_smul`). Its norm is `E.norm` by definition.
* `IsCompleteModule E` gives `CompleteSpace E.carrier` (`Metric.complete_of_cauchySeq_tendsto`).
* The graph of `T` is sequentially closed. If `uₙ → x` and `T uₙ → y`, then for every `z`,
  `⟨z, y⟩ = lim ⟨z, T uₙ⟩ = lim ⟨T⋆z, uₙ⟩ = ⟨T⋆z, x⟩ = ⟨z, T x⟩`
  (`IsLimit.tendsto_inner_right`), so `y = T x`.
* A continuous linear map satisfies `‖T x‖ ≤ ‖T‖ ‖x‖` (`ContinuousLinearMap.le_opNorm`).
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab

open GroupApproximation.HilbertModule Filter Topology

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Closed graph theorem for Hilbert modules.** -/
theorem isBounded_of_isCompleteModule {E F : CStarModule.{v, v} B} (T : Adjointable E F)
    (hE : IsCompleteModule E) (hF : IsCompleteModule F) : T.IsBounded := by
  letI : NormedAddCommGroup E.carrier := E.toNormedAddCommGroup
  letI : NormedAddCommGroup F.carrier := F.toNormedAddCommGroup
  letI : NormedSpace ℂ E.carrier :=
    { norm_smul_le := fun c x => le_of_eq (E.norm_smul c x) }
  letI : NormedSpace ℂ F.carrier :=
    { norm_smul_le := fun c x => le_of_eq (F.norm_smul c x) }
  have nE : ∀ x : E.carrier, ‖x‖ = E.norm x := fun _ => rfl
  have nF : ∀ y : F.carrier, ‖y‖ = F.norm y := fun _ => rfl
  have limE : ∀ (u : ℕ → E.carrier) (a : E.carrier), Tendsto u atTop (𝓝 a) →
      IsLimit E u a := by
    intro u a hu ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [dist_eq_norm_sub, nE] at h
    exact h.le
  have limF : ∀ (u : ℕ → F.carrier) (a : F.carrier), Tendsto u atTop (𝓝 a) →
      IsLimit F u a := by
    intro u a hu ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [dist_eq_norm_sub, nF] at h
    exact h.le
  haveI : CompleteSpace E.carrier := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    have hc : IsCauchy E u := by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
      refine ⟨N, fun m n hm hn => ?_⟩
      have h := hN m hm n hn
      rw [dist_eq_norm_sub, nE] at h
      exact h.le
    obtain ⟨y, hy⟩ := hE u hc
    refine ⟨y, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm_sub, nE]
    exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)
  haveI : CompleteSpace F.carrier := by
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    have hc : IsCauchy F u := by
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
      refine ⟨N, fun m n hm hn => ?_⟩
      have h := hN m hm n hn
      rw [dist_eq_norm_sub, nF] at h
      exact h.le
    obtain ⟨y, hy⟩ := hF u hc
    refine ⟨y, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
    obtain ⟨N, hN⟩ := hy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm_sub, nF]
    exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)
  let g : E.carrier →ₗ[ℂ] F.carrier :=
    { toFun := T.toFun
      map_add' := T.map_add
      map_smul' := fun c x => by
        rw [RingHom.id_apply]
        exact T.map_smul c x }
  have hg : ∀ (u : ℕ → E.carrier) (x : E.carrier) (y : F.carrier),
      Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x := by
    intro u x y hu hgu
    refine F.eq_of_inner_eq fun z => ?_
    have h1 : Tendsto (fun n => F.inner z (T.toFun (u n))) atTop (𝓝 (F.inner z y)) :=
      (limF (g ∘ u) y hgu).tendsto_inner_right z
    have h2 : Tendsto (fun n => F.inner z (T.toFun (u n))) atTop
        (𝓝 (F.inner z (T.toFun x))) := by
      have h3 := (limE u x hu).tendsto_inner_right (T.adj z)
      simpa only [T.inner_adj'] using h3
    exact tendsto_nhds_unique h1 h2
  let f : E.carrier →L[ℂ] F.carrier := ContinuousLinearMap.ofSeqClosedGraph hg
  refine ⟨‖f‖, norm_nonneg f, ?_⟩
  intro x
  have h := f.le_opNorm x
  rw [nE, nF] at h
  exact h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isBounded_of_isCompleteModule

/-- **The closed graph statement holds.** -/
theorem adjointableBounded : AdjointableBoundedStatement B :=
  fun _ _ T hE hF => isBounded_of_isCompleteModule T hE hF

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.adjointableBounded

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab
