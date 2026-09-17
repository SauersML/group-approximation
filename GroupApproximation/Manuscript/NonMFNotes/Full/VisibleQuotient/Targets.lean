import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.Basic
import GroupApproximation.Sofic.TargetEquivalence
import GroupApproximation.Analysis.PeterWeylProfinite
import GroupApproximation.Meta.AxiomGuard

/-!
# `Φ_K` is the universal visible quotient

Manuscript `non_mf_group_notes.tex`, **thm:notes-visible-quotient**, the
universal form (tex lines 1963--2050).  For a finite group `K`, every
homomorphism from `W_K` into one of the approximation targets of the notes
factors uniquely through `Φ_K : W_K → P_K`.  The targets are:

* the genuine norm-matrix corona `∏ M_n / ⊕ M_n`;
* every residually finite group, and so every finite group;
* every finite-dimensional unitary group;
* `GL_d(F)` for every field `F` and every `d`;
* every compact Hausdorff group, and every profinite group.

In each case precomposition with `Φ_K` is a bijection of Hom-sets.  It is
injective because `Φ_K` is onto.  It is surjective because `ker Φ_K` is the
radical of the relevant class (`notesVisibleQuotient`), so every homomorphism
into a target of the class kills it.

Main declarations:

* `precomp_phiK_bijective_actualCorona`, `precomp_phiK_bijective_residuallyFinite`,
  `precomp_phiK_bijective_finite`, `precomp_phiK_bijective_fdUnitary`,
  `precomp_phiK_bijective_generalLinearGroup`, `precomp_phiK_bijective_compact`,
  `precomp_phiK_bijective_profinite`;
* `notesVisibleQuotient_precomp_bijective` -- the corona, residually finite,
  `GL_d(F)` and compact Hausdorff cases together.
-/

namespace GroupApproximation.Full.NN04

open MatricialStabilityRadical

variable (K : Type) [Group K] [Finite K]

/-- **Corona targets.**  Every genuine norm-matrix-corona representation of
`W_K` factors uniquely through `Φ_K`. -/
theorem precomp_phiK_bijective_actualCorona
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    Function.Bijective
      (precomp (PhiK K) (unitary (NormMatrixCStarCorona (fun n ↦ X n)))) := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  apply precomp_bijective _ (phiK_surjective K)
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ actualCoronaMFResidual (WK K) := by
    rw [(notesVisibleQuotient K).2.2.1]
    exact hx
  exact hxrad X hX ρ

/-- **Residually finite targets.** -/
theorem precomp_phiK_bijective_residuallyFinite
    (T : Type) [Group T] (hT : IsResiduallyFinite T) :
    Function.Bijective (precomp (PhiK K) T) := by
  apply precomp_bijective _ (phiK_surjective K)
  apply invisibleTo_of_ker_le_finiteResidual
  · rw [(notesVisibleQuotient K).2.2.2.2.1]
  · exact hT

/-- **Finite targets.** -/
theorem precomp_phiK_bijective_finite (T : Type) [Group T] [Finite T] :
    Function.Bijective (precomp (PhiK K) T) :=
  precomp_phiK_bijective_residuallyFinite K T (isResiduallyFinite_of_finite T)

/-- **Finite-dimensional unitary targets.** -/
theorem precomp_phiK_bijective_fdUnitary (Y : FiniteModel) :
    Function.Bijective (precomp (PhiK K) (Matrix.unitaryGroup Y ℂ)) := by
  apply precomp_bijective _ (phiK_surjective K)
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ fdUnitaryResidual (WK K) := by
    rw [(notesVisibleQuotient K).2.2.2.1]
    exact hx
  exact mem_fdUnitaryResidual_iff.mp hxrad Y ρ

/-- **`GL_d(F)` targets**, for every field `F` and every dimension `d`. -/
theorem precomp_phiK_bijective_generalLinearGroup (F : Type) [Field F] (d : ℕ) :
    Function.Bijective
      (precomp (PhiK K) (Matrix.GeneralLinearGroup (Fin d) F)) := by
  apply precomp_bijective _ (phiK_surjective K)
  apply invisibleTo_generalLinearGroup_of_ker_le_linearResidual
  rw [(notesVisibleQuotient K).2.2.2.2.2.1]

/-- **Compact Hausdorff targets.**  This is the Bohr column: `ker Φ_K` is the
Bohr residual of `W_K`. -/
theorem precomp_phiK_bijective_compact
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [CompactSpace T] [T2Space T] :
    Function.Bijective (precomp (PhiK K) T) := by
  apply precomp_bijective _ (phiK_surjective K)
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ PeterWeyl.bohrResidual (WK K) := by
    rw [(notesVisibleQuotient K).2.2.2.2.2.2]
    exact hx
  exact PeterWeyl.mem_bohrResidual_iff.mp hxrad
    { carrier := T
      group := ‹Group T›
      topology := ‹TopologicalSpace T›
      topGroup := ‹IsTopologicalGroup T›
      compact := ‹CompactSpace T›
      hausdorff := ‹T2Space T› } ρ

/-- **Profinite targets.**  These need no Peter--Weyl input. -/
theorem precomp_phiK_bijective_profinite
    (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [CompactSpace T] [TotallyDisconnectedSpace T] :
    Function.Bijective (precomp (PhiK K) T) := by
  apply precomp_bijective _ (phiK_surjective K)
  intro ρ
  have hfinite := PeterWeyl.finiteResidual_le_ker_of_profinite ρ
  rw [(notesVisibleQuotient K).2.2.2.2.1] at hfinite
  exact hfinite

/-- **thm:notes-visible-quotient, universal form.**  For a finite group `K`,
precomposition with `Φ_K : W_K → P_K` is a bijection of Hom-sets into
the genuine corona, into every residually finite group, into `GL_d(F)` for every
field `F` and dimension `d`, and into every compact Hausdorff group. -/
theorem notesVisibleQuotient_precomp_bijective :
    (∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
      letI : ∀ n, Nonempty (X n) :=
        fun n ↦ Fintype.card_pos_iff.mp (hX n)
      Function.Bijective
        (precomp (PhiK K) (unitary (NormMatrixCStarCorona (fun n ↦ X n))))) ∧
    (∀ (T : Type) [Group T], IsResiduallyFinite T →
      Function.Bijective (precomp (PhiK K) T)) ∧
    (∀ (F : Type) [Field F] (d : ℕ),
      Function.Bijective (precomp (PhiK K) (Matrix.GeneralLinearGroup (Fin d) F))) ∧
    (∀ (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
      [CompactSpace T] [T2Space T], Function.Bijective (precomp (PhiK K) T)) := by
  refine ⟨fun X hX => precomp_phiK_bijective_actualCorona K X hX, ?_, ?_, ?_⟩
  · intro T _ hT
    exact precomp_phiK_bijective_residuallyFinite K T hT
  · intro F _ d
    exact precomp_phiK_bijective_generalLinearGroup K F d
  · intro T _ _ _ _ _
    exact precomp_phiK_bijective_compact K T

#audit_axioms precomp_phiK_bijective_actualCorona
#audit_axioms precomp_phiK_bijective_residuallyFinite
#audit_axioms precomp_phiK_bijective_finite
#audit_axioms precomp_phiK_bijective_fdUnitary
#audit_axioms precomp_phiK_bijective_generalLinearGroup
#audit_axioms precomp_phiK_bijective_compact
#audit_axioms precomp_phiK_bijective_profinite
#audit_axioms notesVisibleQuotient_precomp_bijective

end GroupApproximation.Full.NN04
