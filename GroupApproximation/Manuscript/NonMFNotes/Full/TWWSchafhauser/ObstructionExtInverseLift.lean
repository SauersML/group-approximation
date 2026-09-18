import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtInverseLiftIdeal
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtInverseLiftForm
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebra
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffros
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosClosure
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtCorona
import GroupApproximation.Analysis.CStarIdealApproximateUnit
import GroupApproximation.Analysis.CStarCompletelyPositiveForm
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Completely positive contractive lifts of Busby cycles

Lane `TWWSch-Inv1`, work order `WO-Inv-1`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership`, through the Busby picture of `Ext(S, J)` in Schafhauser's proof
of the Tikuisis--White--Winter theorem.

**`BusbyCycle.exists_cpc_lift`**: for a separable nuclear unital C⋆-algebra `S`, every Busby
cycle `x` agrees modulo compacts with a completely positive contraction `ψ : S → 𝓛(H_J)`.

The Busby map `x.toCorona : S → 𝓛(H_J)/𝒦(H_J)` is a `⋆`-homomorphism, hence completely positive
and contractive. The Choi--Effros lifting theorem (M.-D. Choi, E. G. Effros, *The completely
positive lifting problem for C⋆-algebras*, Ann. of Math. (2) **104** (1976), Thm. 3.10;
N. P. Brown, N. Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm. C.3) lifts it
through the quotient map to a completely positive contraction `ψ : S →ₗ[ℂ] 𝓛(H_J)`, as in
W. Arveson, *Notes on extensions of C⋆-algebras*, Duke Math. J. **44** (1977), §4. The matrix
positivity of `ψ` is converted to the pointwise form `IsCPCOp` by `isCPCOp_of_linearMap`.

When `J` is trivial, `𝓛(H_J)` is trivial and the zero map is a lift.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

/-- **Matrix complete positivity gives the factored Gram form** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`): for a completely positive `ψ` and a tuple `a`, the matrix
`[ψ(aᵢ⋆aⱼ)]` is `P⋆P`, i.e. `ψ(aᵢ⋆aⱼ) = ∑ₖ P(k,i)⋆ P(k,j)`. -/
theorem exists_factor_of_isCompletelyPositive {S B : Type} [CStarAlgebra S] [CStarAlgebra B]
    {ψ : S →ₗ[ℂ] B}
    (hψ : CStarExactness.IsCompletelyPositive ψ) (n : ℕ) (a : Fin n → S) :
    ∃ P : Fin n → Fin n → B, ∀ i j, ψ (star (a i) * a j) = ∑ k, star (P k i) * P k j := by
  cases n with
  | zero => exact ⟨fun _ _ => 0, fun i => i.elim0⟩
  | succ m =>
    obtain ⟨N, hN⟩ := CStarExactness.star_col_mul_col a
    obtain ⟨P, hP⟩ := hψ (m + 1)
      (CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j)) ⟨N, hN⟩
    refine ⟨fun k i => P k i, fun i j => ?_⟩
    have hentry := congrArg (fun M : CStarMatrix (Fin (m + 1)) (Fin (m + 1)) B => M i j) hP
    exact hentry.trans ((CStarExactness.cstarMatrix_mul_apply (star P) P i j).trans
      (Finset.sum_congr rfl fun k _ =>
        congrArg (· * P k j) (CStarExactness.cstarMatrix_star_apply P i k)))

/-- **Completely positive contractive lifts of Busby cycles** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Choi--Effros, Ann. of Math. (2) 104 (1976), Thm. 3.10;
Arveson, Duke Math. J. 44 (1977), §4; Brown--Ozawa, Thm. C.3): for a separable nuclear `S`,
every Busby cycle agrees modulo compacts with a completely positive contraction. -/
theorem BusbyCycle.exists_cpc_lift {S : Type} [CStarAlgebra S]
    (hS : CStarExactness.IsNuclearCStarAlgebra S) [TopologicalSpace.SeparableSpace S]
    {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
    [TopologicalSpace.SeparableSpace J] (x : BusbyCycle S J) :
    ∃ ψ : S → StdOp J, IsCPCOp ψ ∧ ∀ a, CompactEq J (x.lift a) (ψ a) := by
  obtain (_ | _) := subsingleton_or_nontrivial (StdBdd J)
  · have hone : ‖(0 : S →ₗ[ℂ] StdBdd J) 1‖ ≤ 1 := by
      rw [LinearMap.zero_apply]
      exact ((StdBdd.norm_eq_zero_iff' (0 : StdBdd J)).mpr rfl).le.trans zero_le_one
    refine ⟨fun a => ((0 : S →ₗ[ℂ] StdBdd J) a).1,
      isCPCOp_of_linearMap 0 (fun _ => Subsingleton.elim _ _)
        (fun _ _ => ⟨fun _ _ => 0, fun _ _ => Subsingleton.elim _ _⟩) hone,
      fun a => ?_⟩
    have h : x.lift a = ((0 : S →ₗ[ℂ] StdBdd J) a).1 :=
      congrArg Subtype.val (Subsingleton.elim (x.liftBdd a) ((0 : S →ₗ[ℂ] StdBdd J) a))
    show CompactEq J (x.lift a) ((0 : S →ₗ[ℂ] StdBdd J) a).1
    rw [h]
    exact compactEq_refl _
  · obtain ⟨ψ, hψcp, hψc, hψπ⟩ := exists_cpc_lift_of_isNuclear hS
      (CStarTensor.quotientStarMk (stdCptIdeal J))
      (fun y => Ideal.Quotient.mk_surjective (I := stdCptIdeal J) y) _
      (CStarExactness.isCompletelyPositive_of_starAlgHom x.toCorona)
      (fun a => NonUnitalStarAlgHom.norm_apply_le x.toCorona a)
    refine ⟨fun a => (ψ a).1,
      isCPCOp_of_linearMap ψ (map_star_of_isCompletelyPositive hψcp)
        (exists_factor_of_isCompletelyPositive hψcp) ((hψc 1).trans choiEffros_norm_one_le),
      fun a => ?_⟩
    exact (mk_eq_mk_iff_compactEq (x.liftBdd a) (ψ a)).mp (hψπ a).symm

end GroupApproximation.Full.TWWSchafhauser

end
