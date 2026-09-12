import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsItemB
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsItemA
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`, the last paragraph of the proof, at the printed objects

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units` (tex 1290–1294):

> So let `v = e + (1-e)v(1-e)` with `e ≠ 0` and `κ(v) = 0`.  By the definition of `K_1`,
> `diag(v,1,…,1) ∈ EL_n(R)` for some `n ≥ 2`.  With `θ` and `P` as in (b),
> `v = 1 - P + θ(diag(v,1,…,1))`, which lies in `N` by `eq:corner-units`.

The census rows of this paragraph cite `agpStepOne`, which reaches `v ∈ N` by a
two-coordinate route without `θ` or `P`.  `manuscriptSentence_stepOneParagraph` follows the
printed route: the rank `n ≥ 2` from the definition of `K_1`
(`MFQuotientUnitsItemA.manuscriptDiagInElementary`), `θ` and `P` from item (b)
(`MFQuotientUnitsItemB.manuscriptSentence_itemB`), the identity
`v = 1 - P + θ(diag(v,1,…,1))` computed from (b)'s formula, and membership in `N` because
`v` is the value at `diag(v,1,…,1)` of the homomorphism `A ↦ 1 - P + θ(A)` on `EL_n(R)`,
whose range dies in every MF image (Theorem `thm:full-defect-ring` in rank two).
-/

namespace GroupApproximation
namespace MFQuotientUnitsStepOnePrinted

open MFQuotientUnits AlgebraicK RankNElimination

/-- **The printed map `A ↦ 1 - P + θ(A)`** on `EL_n(R)`, for a ring isomorphism
`θ : M_n(R) → PRP`. -/
noncomputable def matrixUnitsHom {R : Type} [Ring R] {P : R} (hP : IsIdempotentElem P)
    {n : ℕ} (θ : Matrix (Fin n) (Fin n) R ≃+* Corner R P hP) :
    elementaryGroup (Fin n) R →* Rˣ :=
  (unitOfCornerUnit P hP).comp
    ((Units.map θ.toMonoidHom).comp (elementaryGroup (Fin n) R).subtype)

/-- **Printed paragraph (tex 1290–1294).**  For `v = e + (1-e)v(1-e)` with `e ≠ 0` and
`κ(v) = 0` in a countable purely infinite simple ring: `diag(v,1,…,1) ∈ EL_n(R)` for some
`n ≥ 2`; with `θ` and `P` as in (b) (so `P = r_1 + ⋯ + r_n`, `r_1 = 1 - e + f`, and `θ`
sends `diag(v,1,…,1)` to `(1-e)v(1-e) + f + r_2 + ⋯ + r_n`), `v = 1 - P + θ(diag(v,1,…,1))`,
this is the value of the homomorphism `A ↦ 1 - P + θ(A)` at `diag(v,1,…,1)`, and `v ∈ N`. -/
def PrintedStepOneParagraph : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (v : Rˣ) (e : R), IsIdempotentElem e → e ≠ 0 →
      (v : R) = e + (1 - e) * (v : R) * (1 - e) → kappa R v = 1 →
        ∃ (n : ℕ) (hn : 2 ≤ n)
          (hdiag : diagAt (⟨0, by omega⟩ : Fin n) v ∈ elementaryGroup (Fin n) R)
          (P : R) (hP : IsIdempotentElem P) (θ : Matrix (Fin n) (Fin n) R ≃+* Corner R P hP),
          (∃ (f : R) (r : Fin n → R), P = ∑ i, r i ∧ r ⟨0, by omega⟩ = 1 - e + f ∧
            ((θ (diagAt (⟨0, by omega⟩ : Fin n) v : Matrix (Fin n) (Fin n) R) :
                Corner R P hP) : R) =
              (1 - e) * (v : R) * (1 - e) + f +
                ∑ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n), r i) ∧
          (v : R) = 1 - P + ((θ (diagAt (⟨0, by omega⟩ : Fin n) v :
            Matrix (Fin n) (Fin n) R) : Corner R P hP) : R) ∧
          matrixUnitsHom hP θ ⟨diagAt (⟨0, by omega⟩ : Fin n) v, hdiag⟩ = v ∧
          v ∈ mfHomKernel Rˣ

theorem manuscriptSentence_stepOneParagraph : PrintedStepOneParagraph := by
  intro R _ _ hR v e he hne hv hκ
  obtain ⟨n, hn, hdiag⟩ := MFQuotientUnitsItemA.manuscriptDiagInElementary R hR v hκ
  obtain ⟨f, r, -, -, -, -, -, -, -, hr0, P, hP, θ, hPsum, hθ⟩ :=
    MFQuotientUnitsItemB.manuscriptSentence_itemB R hR e he hne n hn
  have hval : (v : R) = 1 - P + ((θ (diagAt (⟨0, by omega⟩ : Fin n) v :
      Matrix (Fin n) (Fin n) R) : Corner R P hP) : R) := by
    rw [hθ v hv, hPsum,
      ← Finset.add_sum_erase Finset.univ r (Finset.mem_univ (⟨0, by omega⟩ : Fin n)), hr0]
    nth_rewrite 1 [hv]
    abel
  have hunit : matrixUnitsHom hP θ ⟨diagAt (⟨0, by omega⟩ : Fin n) v, hdiag⟩ = v := by
    apply Units.ext
    rw [hval]
    rfl
  have hmem : v ∈ mfHomKernel Rˣ := by
    rw [← hunit]
    exact cornerUnitSubgroup_le_mfHomKernel
      Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
      R (elementaryRange_le_cornerUnitSubgroup hR hn (matrixUnitsHom hP θ) ⟨_, rfl⟩)
  exact ⟨n, hn, hdiag, P, hP, θ, ⟨f, r, hPsum, hr0, hθ v hv⟩, hval, hunit, hmem⟩

end MFQuotientUnitsStepOnePrinted
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsStepOnePrinted.manuscriptSentence_stepOneParagraph
