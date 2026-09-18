import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetCommutativeHomotopyEssNorm
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetCommutativeHomotopyCore

/-!
# Homotopy invariance of `Ext(-, J)` for nuclear sources

Lane `TWWSch3d3-3C1`, work order `WO-TWWSch3d3-3C` §3C1. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378). Homotopic `⋆`-homomorphisms `f ≃ g : A → B` out of
a separable nuclear `A` induce the same map `f^* = g^* : Ext(B, J) → Ext(A, J)` (G. G. Kasparov,
Izv. Akad. Nauk SSSR 44 (1980), §7; B. Blackadar, *K-theory for operator algebras*, 15.8, 17.6).

For a cycle `x` over `B` and a homotopy `p`, the pulled-back cycles `x ∘ p_t` form an
essential-norm continuous path: `x(p_t a) - x(p_{t₀} a) ≡ x(p_t a - p_{t₀} a)` modulo compacts
(`BusbyCycle.exists_compact_opNorm_sub_sub_le`), and the Busby map is contractive into the
corona (`BusbyCycle.exists_compact_opNorm_sub_le`). The Kasparov core
`ExtGroup.mk_eq_of_isEssNormContinuousPath` then identifies the classes at `t = 0` and `t = 1`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Homotopy

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- Pulling a cycle back along a homotopy gives an essential-norm continuous path of cycles
(`thm:fixed-radical-membership`). -/
theorem BusbyCycle.isEssNormContinuousPath_comap {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (x : BusbyCycle B J) {p : ℝ → (A →⋆ₐ[ℂ] B)} (hp : ∀ a : A, Continuous fun t : ℝ => p t a) :
    BusbyCycle.IsEssNormContinuousPath (fun t : ℝ => x.comap (p t : A →⋆ₙₐ[ℂ] B)) := by
  intro a t₀ ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp (hp a) t₀ (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨K, hK, hKn⟩ := x.exists_compact_opNorm_sub_le (p t a - p t₀ a) (half_pos hε)
  obtain ⟨K', hK', hK'n⟩ := x.exists_compact_opNorm_sub_sub_le (p t a) (p t₀ a) hK hKn
  have hd : ‖p t a - p t₀ a‖ < ε / 2 := by
    rw [← dist_eq_norm_sub]
    exact hδε t (by rw [Real.dist_eq]; exact ht)
  refine ⟨K', hK', ?_⟩
  show (Adjointable.sub (Adjointable.sub (x.lift (p t a)) (x.lift (p t₀ a))) K').opNorm ≤ ε
  linarith

end Homotopy

/-- **Homotopy invariance of `Ext(-, J)` for nuclear sources.** Homotopic `⋆`-homomorphisms
`f ≃ g : A → B` with `A` separable nuclear induce the same pull-back on `Ext(-, J)`
(Kasparov 1980, §7; Blackadar 15.8, 17.6; `thm:fixed-radical-membership`). -/
theorem ExtGroup.comap_eq_of_homotopic {A B : KK.SepCStarAlgebra.{0}}
    (hA : GroupApproximation.CStarExactness.IsNuclearCStarAlgebra A) {f g : A →⋆ₐ[ℂ] B}
    (h : KK.Homotopic f g) (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J]
    [StarOrderedRing J] [TopologicalSpace.SeparableSpace J] :
    (ExtGroup.comap (f : A →⋆ₙₐ[ℂ] B) : ExtGroup B J →+ ExtGroup A J) =
      ExtGroup.comap (g : A →⋆ₙₐ[ℂ] B) := by
  obtain ⟨p, hp, rfl, rfl⟩ := h
  exact ExtGroup.comap_eq_of_forall_mk fun x =>
    ExtGroup.mk_eq_of_isEssNormContinuousPath hA (x.isEssNormContinuousPath_comap hp)

end GroupApproximation.Full.TWWSchafhauser
