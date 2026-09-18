import GroupApproximation.Manuscript.SpectralPaper.IntroCarto13PhiKRadical
import GroupApproximation.Meta.AxiomGuard

/-!
# Every approximation-class homomorphism factors uniquely through `Φ_K`

Notes census, `thm:notes-visible-quotient` (`non_mf_group_notes.tex` ~1966):

> For every finite group `K`, every homomorphism from `W_K` to a norm matrix
> corona factors uniquely through `Φ_K`.  Moreover
> `ker Φ_K = Rad_MF = Rad_fd = Res_fin = Rad_lin = Rad_Bohr`.

Route.  `Φ_K` is onto (`heightAbelianization_surjective`).  Each target class
has a radical equal to `ker Φ_K` (`five_radicals_eq_ker_heightAbelianization`),
so `ker Φ_K` is invisible to that class.  `precomp_bijective` then turns this
into a bijection `Hom(P_K, T) ≃ Hom(W_K, T)`: existence by descent, uniqueness
by surjectivity.  The classes are genuine norm-matrix coronas, residually finite
groups, finite groups, `U(d)`, `GL_d(F)`, profinite groups and compact Hausdorff
groups.

`NotesVisibleQuotientStatement` bundles, for every finite `K`, four facts:
surjectivity, the kernel as a normal closure, the five radical identities, and
the corona factorization.  `notesVisibleQuotientStatement_holds` proves it
unconditionally.
-/

namespace GroupApproximation.SpectralPaper.IntroCarto13

open SemidirectProduct MarkedCompression ExplicitLinearModel LiteralDoublingWreath
open FinitePerfectLamp GroupApproximation.WreathLampPushforward GroupApproximation.Full.NN04
open MatricialStabilityRadical

/-- **Corona factorization.**  Every norm-matrix-corona representation of `W_K`
factors uniquely through `Φ_K`. -/
theorem heightAbelianization_precomp_bijective_actualCorona (K : Type) [Group K]
    [Finite K] (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    Function.Bijective
      (precomp (heightAbelianization K)
        (unitary (NormMatrixCStarCorona (fun n ↦ X n)))) := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  apply precomp_bijective _ (heightAbelianization_surjective K)
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ actualCoronaMFResidual (WFin K) :=
    (five_radicals_eq_ker_heightAbelianization K).1.ge hx
  exact hxrad X hX ρ

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_precomp_bijective_actualCorona

/-- Residually finite targets. -/
theorem heightAbelianization_precomp_bijective_residuallyFinite (K : Type) [Group K]
    [Finite K] (T : Type) [Group T] (hT : IsResiduallyFinite T) :
    Function.Bijective (precomp (heightAbelianization K) T) :=
  precomp_bijective _ (heightAbelianization_surjective K)
    (invisibleTo_of_ker_le_finiteResidual _
      (five_radicals_eq_ker_heightAbelianization K).2.2.1.ge hT)

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_precomp_bijective_residuallyFinite

/-- Finite targets. -/
theorem heightAbelianization_precomp_bijective_finite (K : Type) [Group K] [Finite K]
    (T : Type) [Group T] [Finite T] :
    Function.Bijective (precomp (heightAbelianization K) T) :=
  heightAbelianization_precomp_bijective_residuallyFinite K T
    (isResiduallyFinite_of_finite T)

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_precomp_bijective_finite

/-- Finite-dimensional unitary targets. -/
theorem heightAbelianization_precomp_bijective_fdUnitary (K : Type) [Group K]
    [Finite K] (Y : FiniteModel) :
    Function.Bijective
      (precomp (heightAbelianization K) (Matrix.unitaryGroup Y ℂ)) := by
  apply precomp_bijective _ (heightAbelianization_surjective K)
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ fdUnitaryResidual (WFin K) :=
    (five_radicals_eq_ker_heightAbelianization K).2.1.ge hx
  exact mem_fdUnitaryResidual_iff.mp hxrad Y ρ

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_precomp_bijective_fdUnitary

/-- `GL_d(F)` targets, for every field and dimension. -/
theorem heightAbelianization_precomp_bijective_generalLinearGroup (K : Type) [Group K]
    [Finite K] (F : Type) [Field F] (d : ℕ) :
    Function.Bijective
      (precomp (heightAbelianization K) (Matrix.GeneralLinearGroup (Fin d) F)) :=
  precomp_bijective _ (heightAbelianization_surjective K)
    (invisibleTo_generalLinearGroup_of_ker_le_linearResidual _
      (five_radicals_eq_ker_heightAbelianization K).2.2.2.1.ge)

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_precomp_bijective_generalLinearGroup

/-- Profinite targets. -/
theorem heightAbelianization_precomp_bijective_profinite (K : Type) [Group K]
    [Finite K] (T : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [CompactSpace T] [TotallyDisconnectedSpace T] :
    Function.Bijective (precomp (heightAbelianization K) T) := by
  apply precomp_bijective _ (heightAbelianization_surjective K)
  intro ρ
  exact (five_radicals_eq_ker_heightAbelianization K).2.2.1.ge.trans
    (PeterWeyl.finiteResidual_le_ker_of_profinite ρ)

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_precomp_bijective_profinite

/-- Compact Hausdorff targets. -/
theorem heightAbelianization_precomp_bijective_compact (K : Type) [Group K] [Finite K]
    (C : PeterWeyl.CompactTarget.{0}) :
    Function.Bijective (precomp (heightAbelianization K) C.carrier) := by
  apply precomp_bijective _ (heightAbelianization_surjective K)
  intro ρ x hx
  rw [MonoidHom.mem_ker]
  have hxrad : x ∈ PeterWeyl.bohrResidual (WFin K) :=
    (five_radicals_eq_ker_heightAbelianization K).2.2.2.2.ge hx
  exact PeterWeyl.mem_bohrResidual_iff.mp hxrad C ρ

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.heightAbelianization_precomp_bijective_compact

/-- **The notes' visible-quotient theorem, for every finite lamp group.** -/
def NotesVisibleQuotientStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Function.Surjective (heightAbelianization K) ∧
      (heightAbelianization K).ker =
        Subgroup.normalClosure (commutatorLamps K ∪ heightDiffs K) ∧
      (actualCoronaMFResidual (WFin K) = (heightAbelianization K).ker ∧
        fdUnitaryResidual (WFin K) = (heightAbelianization K).ker ∧
          finiteResidual (WFin K) = (heightAbelianization K).ker ∧
            linearResidual (WFin K) = (heightAbelianization K).ker ∧
              PeterWeyl.bohrResidual (WFin K) = (heightAbelianization K).ker) ∧
      ∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
        letI : ∀ n, Nonempty (X n) :=
          fun n ↦ Fintype.card_pos_iff.mp (hX n)
        Function.Bijective
          (precomp (heightAbelianization K)
            (unitary (NormMatrixCStarCorona (fun n ↦ X n))))

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.NotesVisibleQuotientStatement

/-- **Closed.** -/
theorem notesVisibleQuotientStatement_holds : NotesVisibleQuotientStatement := by
  intro K _ _
  exact ⟨heightAbelianization_surjective K, ker_heightAbelianization_eq_union K,
    five_radicals_eq_ker_heightAbelianization K,
    fun X hX => heightAbelianization_precomp_bijective_actualCorona K X hX⟩

#audit_axioms GroupApproximation.SpectralPaper.IntroCarto13.notesVisibleQuotientStatement_holds

end GroupApproximation.SpectralPaper.IntroCarto13
