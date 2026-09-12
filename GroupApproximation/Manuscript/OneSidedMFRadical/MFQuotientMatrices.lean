import GroupApproximation.Algebra.PurelyInfiniteWholeRingCornerUnits
import GroupApproximation.Algebra.PurelyInfiniteMatrixEmbedding
import GroupApproximation.KOne.UnstableKOneAbelian
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnits
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional

/-!
# The maximal MF quotient of `GL_n(R)`, for every `n ≥ 2`

For a countable purely infinite simple ring, this module proves

  `mfHomKernel GL_n(R) = [GL_n(R), GL_n(R)] = EL_n(R)`.

The commutator subgroup itself has full MF radical, the abelianization is MF,
and every homomorphism to an MF group factors uniquely through abelianization.
There are no Ara--Goodearl--Pardo or Menal--Moncasi hypotheses in these results.

The proof is the three-inclusion argument, now for every such ring:
single-sandwich division and rank-n elimination give `[GL_n,GL_n] ≤ EL_n`;
the full-defect theorem gives `EL_n ≤ mfHomKernel GL_n`; and the countable
abelianization gives `mfHomKernel GL_n ≤ [GL_n,GL_n]`.

This closes the group-theoretic classification in `thm:mf-quotient-units` at
every rank at least two. The rank-one statement and identification of the
abelianization with the constructed algebraic `K₁(R)` are separate obligations.
Neither is inferred from the fact that the quotient below is abelian.
-/

namespace GroupApproximation
namespace MFQuotientMatrices

open MFQuotientUnits
open Manuscript.OneSidedMFRadical

/-- A countable group's MF-hom kernel lies in its commutator subgroup. -/
theorem mfHomKernel_le_commutator (G : Type) [Group G] [Countable G] :
    mfHomKernel G ≤ commutator G := by
  haveI : Countable (Abelianization G) :=
    (QuotientGroup.mk'_surjective (commutator G)).countable
  intro x hx
  have h : x ∈ (Abelianization.of : G →* Abelianization G).ker :=
    (mem_mfHomKernel_iff x).mp hx _ (countableAbelianMF _) Abelianization.of
  rwa [Abelianization.ker_of] at h

section MatrixGroups

variable (R : Type) [Ring R] [Countable R]
variable (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) (hn : 2 ≤ n)

include hR hn

/-- The elementary group itself has full MF radical, in all characteristics. -/
theorem elementary_full_mf_radical :
    mfHomKernel (elementaryGroup (Fin n) R) = ⊤ := by
  haveI := hR.isSimpleRing
  obtain ⟨s, t, hts, hne⟩ := exists_unitProperIsometry hR
  obtain ⟨m, a, b, hab⟩ := isFiniteMultipleSum_one_of_isSimpleRing hne
  apply mfHomKernel_eq_top_iff.mpr
  intro M _ hM f x
  exact FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
    R s t hts ⟨m, a, b, hab.symm⟩ n hn M hM f x

/-- Every homomorphism from `GL_n(R)` to an MF group kills `EL_n(R)`. -/
theorem elementary_le_mfHomKernel :
    elementaryGroup (Fin n) R ≤ mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ := by
  intro x hx
  apply (mem_mfHomKernel_iff x).mpr
  intro M _ hM f
  exact mfHomKernel_eq_top_iff.mp (elementary_full_mf_radical R hR n hn)
    M hM (f.comp (elementaryGroup (Fin n) R).subtype) ⟨x, hx⟩

/-- **The exact MF radical of `GL_n(R)` at every rank `n ≥ 2`.** -/
theorem mfHomKernel_matrixUnits_eq :
    mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ =
        commutator (Matrix (Fin n) (Fin n) R)ˣ ∧
      commutator (Matrix (Fin n) (Fin n) R)ˣ = elementaryGroup (Fin n) R := by
  haveI := hR.isSimpleRing
  haveI : Countable (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (Countable (Fin n → Fin n → R))
  haveI : Countable (Matrix (Fin n) (Fin n) R)ˣ :=
    Function.Injective.countable
      (f := (Units.val : (Matrix (Fin n) (Fin n) R)ˣ → Matrix (Fin n) (Fin n) R))
      (fun _ _ h ↦ Units.ext h)
  have hindices : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hcomm : commutator (Matrix (Fin n) (Fin n) R)ˣ ≤
      elementaryGroup (Fin n) R :=
    RankNElimination.commutator_le_elementaryGroup
      (fun a ha ↦ exists_sandwich_of_isPurelyInfiniteSimpleRing hR ha) hindices
  have hEL := elementary_le_mfHomKernel R hR n hn
  have hN := mfHomKernel_le_commutator (Matrix (Fin n) (Fin n) R)ˣ
  exact ⟨le_antisymm hN (hcomm.trans hEL), le_antisymm hcomm (hEL.trans hN)⟩

/-- The commutator group is intrinsically MF-invisible, not only invisible
under homomorphisms defined on the ambient general linear group. -/
theorem commutator_full_mf_radical :
    mfHomKernel (commutator (Matrix (Fin n) (Fin n) R)ˣ) = ⊤ := by
  rw [(mfHomKernel_matrixUnits_eq R hR n hn).2]
  exact elementary_full_mf_radical R hR n hn

/-- **The universal property of the maximal MF quotient.** -/
theorem factors_uniquely_through_abelianization
    (M : Type) [Group M] (hM : IsOperatorMF M)
    (f : (Matrix (Fin n) (Fin n) R)ˣ →* M) :
    ∃! g : Abelianization (Matrix (Fin n) (Fin n) R)ˣ →* M,
      g.comp Abelianization.of = f := by
  have hf : commutator (Matrix (Fin n) (Fin n) R)ˣ ≤ f.ker := by
    intro x hx
    have hxN : x ∈ mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ := by
      rwa [(mfHomKernel_matrixUnits_eq R hR n hn).1]
    exact (mem_mfHomKernel_iff x).mp hxN M hM f
  refine ⟨QuotientGroup.lift _ f hf, ?_, ?_⟩
  · exact MonoidHom.ext fun _ ↦ rfl
  · intro g hg
    apply MonoidHom.ext
    intro x
    obtain ⟨u, rfl⟩ :=
      QuotientGroup.mk'_surjective (commutator (Matrix (Fin n) (Fin n) R)ˣ) x
    exact DFunLike.congr_fun hg u

end MatrixGroups

/-- **The matrix-group MF quotient classification**, with no literature inputs.
The name deliberately records the rank restriction and quotient used here. -/
def PrintedMFQuotientMatrices : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ n : ℕ, 2 ≤ n →
      mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ =
          commutator (Matrix (Fin n) (Fin n) R)ˣ ∧
        commutator (Matrix (Fin n) (Fin n) R)ˣ = elementaryGroup (Fin n) R ∧
        mfHomKernel (commutator (Matrix (Fin n) (Fin n) R)ˣ) = ⊤ ∧
        IsOperatorMF (Abelianization (Matrix (Fin n) (Fin n) R)ˣ) ∧
        Nonempty ((Matrix (Fin n) (Fin n) R)ˣ ⧸
          mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ ≃*
            Abelianization (Matrix (Fin n) (Fin n) R)ˣ) ∧
        ∀ (M : Type) [Group M], IsOperatorMF M →
          ∀ f : (Matrix (Fin n) (Fin n) R)ˣ →* M,
            ∃! g : Abelianization (Matrix (Fin n) (Fin n) R)ˣ →* M,
              g.comp Abelianization.of = f

/-- The complete classification in `PrintedMFQuotientMatrices`. -/
theorem manuscriptMFQuotientMatrices : PrintedMFQuotientMatrices := by
  intro R _ _ hR n hn
  haveI : Countable (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (Countable (Fin n → Fin n → R))
  haveI : Countable (Matrix (Fin n) (Fin n) R)ˣ :=
    Function.Injective.countable
      (f := (Units.val : (Matrix (Fin n) (Fin n) R)ˣ → Matrix (Fin n) (Fin n) R))
      (fun _ _ h ↦ Units.ext h)
  haveI : Countable (Abelianization (Matrix (Fin n) (Fin n) R)ˣ) :=
    (QuotientGroup.mk'_surjective (commutator (Matrix (Fin n) (Fin n) R)ˣ)).countable
  obtain ⟨hN, hE⟩ := mfHomKernel_matrixUnits_eq R hR n hn
  exact ⟨hN, hE, commutator_full_mf_radical R hR n hn, countableAbelianMF _,
    ⟨QuotientGroup.quotientMulEquivOfEq hN⟩,
    fun M _ hM f ↦ factors_uniquely_through_abelianization R hR n hn M hM f⟩

end MFQuotientMatrices
end GroupApproximation

#audit_closed_axioms GroupApproximation.MFQuotientMatrices.manuscriptMFQuotientMatrices
#audit_axioms GroupApproximation.MFQuotientMatrices.commutator_full_mf_radical
