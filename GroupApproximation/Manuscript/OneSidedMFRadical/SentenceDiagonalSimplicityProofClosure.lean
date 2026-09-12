import GroupApproximation.Leavitt.ElementaryTransvectionExtraction
import GroupApproximation.Leavitt.RootDetectionBinary
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence closure of the diagonal simplicity branch

The diagonal branch of `prop:simple` passes through three scalar statements
before extracting a root.  They are kept visible here, followed by the exact
coefficient chosen in the paper and the normal-subgroup membership of its
commutator.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open ElementarySimplicity
open RootDetectionBinary
open scoped commutatorElement

universe u v

/-- The three successive scalar conclusions in the printed diagonal
argument. -/
def PrintedDiagonalScalarSequence : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [Ring S] (g : elementaryGroup ι S),
    (∀ p q : ι, p ≠ q → elMat g p q = 0) →
      (∀ (i j : ι) (hij : i ≠ j) (a : S),
        g * elGen i j hij a = elGen i j hij a * g) →
        (∀ (i j : ι) (_hij : i ≠ j), elMat g i i = elMat g j j) ∧
          (∃ lam : S, (∃ mu : S, lam * mu = 1 ∧ mu * lam = 1) ∧
            elMat g = Matrix.diagonal fun _ : ι ↦ lam) ∧
          ∀ i : ι,
            (∀ a : S, elMat g i i * a = a * elMat g i i) ∧
              ∃ mu : S,
                elMat g i i * mu = 1 ∧ mu * elMat g i i = 1

theorem manuscriptDiagonalScalarSequence : PrintedDiagonalScalarSequence := by
  intro ι S _ _ _ _ g hdiag hcomm
  exact ⟨fun i j hij ↦ elMat_diag_eq_of_commute_elGen g hdiag hcomm hij,
    exists_unit_elMat_eq_diagonal_of_commute_elGen g hdiag hcomm,
    fun i ↦ elMat_diag_central_unit_of_commute_elGen g hdiag hcomm i⟩

/-- The final diagonal sentence with the paper's literal coefficient
`x = λ_i a λ_j⁻¹ - a`, its nonvanishing, the commutator identity, and normal
subgroup membership all retained. -/
def PrintedDiagonalExplicitRootExtraction : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [Ring S],
    (∀ lam : S, (∀ z : S, lam * z = z * lam) →
      (∃ mu : S, lam * mu = 1 ∧ mu * lam = 1) → lam = 1) →
      ∀ (N : Subgroup (elementaryGroup ι S)) [N.Normal]
        (g : elementaryGroup ι S),
        g ∈ N → g ≠ 1 →
          (∀ p q : ι, p ≠ q → elMat g p q = 0) →
            ∃ (i j : ι) (hij : i ≠ j) (a : S),
              let x := elMat g i i * (a * elMat (g⁻¹) j j) - a
              x ≠ 0 ∧
                g * elGen i j hij a * g⁻¹ * (elGen i j hij a)⁻¹ =
                  elGen i j hij x ∧
                elGen i j hij x ∈ N

theorem manuscriptDiagonalExplicitRootExtraction :
    PrintedDiagonalExplicitRootExtraction := by
  intro ι S _ _ _ _ hcentral N _ g hg hgne hdiag
  by_cases hall : ∀ i j : ι, i ≠ j → ∀ a : S,
      elMat g i i * (a * elMat (g⁻¹) j j) = a
  · exfalso
    apply hgne
    have hcomm : ∀ (i j : ι) (hij : i ≠ j) (a : S),
        g * elGen i j hij a = elGen i j hij a * g :=
      fun i j hij a ↦
        (commute_elGen_iff_diag_relation g hdiag hij a).mpr
          (hall i j hij a)
    obtain ⟨lam, ⟨mu, hlamMu, hmuLam⟩, hscalar⟩ :=
      exists_unit_elMat_eq_diagonal_of_commute_elGen g hdiag hcomm
    obtain ⟨k, -, -⟩ := exists_pair_ne ι
    have hk : elMat g k k = lam := by
      rw [hscalar, Matrix.diagonal_apply, if_pos (rfl : k = k)]
    have hcentralLam : ∀ a : S, lam * a = a * lam := by
      intro a
      have h := (elMat_diag_central_unit_of_commute_elGen
        g hdiag hcomm k).1 a
      rwa [hk] at h
    have hlam : lam = 1 :=
      hcentral lam hcentralLam ⟨mu, hlamMu, hmuLam⟩
    apply elMat_injective
    rw [elMat_one]
    ext i j
    rw [hscalar, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, hlam]
    · rw [if_neg hij, if_neg hij]
  · push Not at hall
    obtain ⟨i, j, hij, a, ha⟩ := hall
    let x := elMat g i i * (a * elMat (g⁻¹) j j) - a
    have hx : x ≠ 0 := by
      exact sub_ne_zero_of_ne ha
    have hinv : (elGen i j hij a)⁻¹ = elGen (R := S) i j hij (-a) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [elGen_mul, add_neg_cancel, elGen_zero]
    have heq : g * elGen i j hij a * g⁻¹ * (elGen i j hij a)⁻¹ =
        elGen i j hij x := by
      rw [conj_elGen_of_diagonal g hdiag hij a, hinv, elGen_mul]
      simp only [x, sub_eq_add_neg]
    have hmem : g * elGen i j hij a * g⁻¹ * (elGen i j hij a)⁻¹ ∈ N := by
      simpa only [commutatorElement_def] using
        (commutator_mem_left N hg (elGen i j hij a))
    exact ⟨i, j, hij, a, hx, heq, heq ▸ hmem⟩

#audit_closed_axioms manuscriptDiagonalScalarSequence
#audit_closed_axioms manuscriptDiagonalExplicitRootExtraction

end OneSidedMFRadical
end Manuscript
end GroupApproximation
