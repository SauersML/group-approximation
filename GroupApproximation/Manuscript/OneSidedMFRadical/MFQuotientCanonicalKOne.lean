import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaProof

/-!
# The canonical maximal MF quotient at every matrix rank

For every countable purely infinite simple ring R and every n ≥ 1, the
canonical map GL_n(R) → K₁(R) is surjective, its kernel is the commutator
subgroup and the exact MF-hom kernel, and every map to an MF group factors
uniquely through it. This is the printed base-ring conclusion, with all
inputs discharged.

The proof works directly with finite matrices and their classes in the
stable group. General Morita invariance for arbitrary rings is not needed.
-/

namespace GroupApproximation
namespace MFQuotientUnitsKOne

open AlgebraicK RankNElimination MFQuotientUnits KappaProof

variable (R : Type) [Ring R]

/-- The actual canonical map from a finite general linear group into the
stable algebraic K₁ of its coefficient ring. -/
noncomputable def matrixKappa (n : ℕ) :
    (Matrix (Fin n) (Fin n) R)ˣ →* AlgebraicKOne R :=
  (QuotientGroup.mk' (elementaryColim R)).comp (glColimOf R n)

theorem matrixKappa_eq_one_of_mem_elementary {n : ℕ}
    {A : (Matrix (Fin n) (Fin n) R)ˣ} (hA : A ∈ elementaryGroup (Fin n) R) :
    matrixKappa R n A = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (glColimOf_mem_elementaryColim (R := R) hA)

theorem matrixKappa_diagAt (n : ℕ) (hn : 0 < n) (u : Rˣ) :
    matrixKappa R n (diagAt (⟨0, hn⟩ : Fin n) u) = kappa R u := by
  rw [← glStab_one_eq_diagAt n hn (by omega) u]
  change QuotientGroup.mk' (elementaryColim R)
    (glColimOf R n (glStab R 1 n (by omega) (unitsToGLOne R u))) = _
  rw [glColimOf_glStab]
  rfl

variable [Countable R]

theorem matrixKappa_surjective (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) (hn : 1 ≤ n) : Function.Surjective (matrixKappa R n) := by
  intro z
  obtain ⟨u, rfl⟩ := (agpUnitKappa R hR).1 z
  exact ⟨diagAt (⟨0, by omega⟩ : Fin n) u, matrixKappa_diagAt R n (by omega) u⟩

/-- The canonical finite-rank K₁ map has exactly the commutator kernel. -/
theorem matrixKappa_ker (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) (hn : 1 ≤ n) :
    (matrixKappa R n).ker = commutator (Matrix (Fin n) (Fin n) R)ˣ := by
  haveI := hR.isSimpleRing
  apply le_antisymm
  · intro A hA
    change matrixKappa R n A = 1 at hA
    obtain ⟨E, hE, F, hF, u, hEF⟩ := exists_elementary_mul_diagAt
      (fun a ha => exists_sandwich_of_isPurelyInfiniteSimpleRing hR ha)
      A (⟨0, by omega⟩ : Fin n)
    have hu : kappa R u = 1 := by
      rw [← matrixKappa_diagAt R n (by omega) u, ← hEF,
        map_mul, map_mul, matrixKappa_eq_one_of_mem_elementary R hE,
        matrixKappa_eq_one_of_mem_elementary R hF, hA, one_mul, mul_one]
    have hucomm : u ∈ commutator Rˣ := by
      rw [← (agpUnitKappa R hR).2]
      exact hu
    have hd : diagAt (⟨0, by omega⟩ : Fin n) u ∈
        commutator (Matrix (Fin n) (Fin n) R)ˣ :=
      map_mem_commutator (diagAtHom (⟨0, by omega⟩ : Fin n)) hucomm
    have hAeq : A = E⁻¹ * diagAt (⟨0, by omega⟩ : Fin n) u * F⁻¹ := by
      rw [← hEF]; group
    rw [hAeq]
    exact mul_mem (mul_mem (inv_mem (elementary_le_commutator R hR n hE)) hd)
      (inv_mem (elementary_le_commutator R hR n hF))
  · rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

theorem mfHomKernel_eq_matrixKappa_ker (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) (hn : 1 ≤ n) :
    mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ = (matrixKappa R n).ker := by
  rw [matrixKappa_ker R hR n hn]
  exact (manuscriptMFQuotientUnits R hR n hn).1

/-- The canonical quotient isomorphism induced by finite-rank stabilization. -/
noncomputable def matrixMFQuotientEquiv (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) (hn : 1 ≤ n) :
    (Matrix (Fin n) (Fin n) R)ˣ ⧸ mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ ≃*
      AlgebraicKOne R :=
  (QuotientGroup.quotientMulEquivOfEq (mfHomKernel_eq_matrixKappa_ker R hR n hn)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (matrixKappa R n)
      (matrixKappa_surjective R hR n hn))

@[simp] theorem matrixMFQuotientEquiv_mk (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) (hn : 1 ≤ n) (A : (Matrix (Fin n) (Fin n) R)ˣ) :
    matrixMFQuotientEquiv R hR n hn (QuotientGroup.mk A) = matrixKappa R n A := rfl

/-- **Every homomorphism to any MF target factors uniquely through the
canonical K₁ map**, uniformly in the positive matrix rank. -/
theorem factors_uniquely_through_matrixKappa (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) (hn : 1 ≤ n) (M : Type) [Group M] (hM : IsOperatorMF M)
    (f : (Matrix (Fin n) (Fin n) R)ˣ →* M) :
    ∃! g : AlgebraicKOne R →* M, g.comp (matrixKappa R n) = f := by
  let κ := matrixKappa R n
  have hsurj := matrixKappa_surjective R hR n hn
  let e := QuotientGroup.quotientKerEquivOfSurjective κ hsurj
  have hsymm : ∀ u, e.symm (κ u) =
      (QuotientGroup.mk u : (Matrix (Fin n) (Fin n) R)ˣ ⧸ κ.ker) := by
    intro u
    have he : e (QuotientGroup.mk u) = κ u := rfl
    rw [← he]
    exact e.symm_apply_apply _
  have hf : κ.ker ≤ f.ker := by
    intro x hx
    have hxN : x ∈ mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ := by
      rw [mfHomKernel_eq_matrixKappa_ker R hR n hn]
      exact hx
    exact (mem_mfHomKernel_iff x).mp hxN M hM f
  have hval : ∀ u, QuotientGroup.lift κ.ker f hf (e.symm (κ u)) = f u := by
    intro u
    rw [hsymm u]
    exact QuotientGroup.lift_mk' _ hf u
  refine ⟨(QuotientGroup.lift κ.ker f hf).comp e.symm.toMonoidHom, ?_, ?_⟩
  · exact MonoidHom.ext fun u => hval u
  · intro g hg
    apply MonoidHom.ext
    intro z
    obtain ⟨u, rfl⟩ := hsurj z
    exact (DFunLike.congr_fun hg u).trans (hval u).symm

/-- **The printed base-ring K₁ conclusion at every positive rank**, without
AGP or Morita input propositions. -/
theorem manuscriptMFQuotientUnitsKOneAtBaseRing : PrintedMFQuotientUnitsKOneAtBaseRing := by
  intro R _ _ hR n hn
  exact ⟨(manuscriptMFQuotientUnits R hR n hn).1, ⟨matrixMFQuotientEquiv R hR n hn⟩⟩

/-- The complete canonical classification, including the quotient map and
the universal property, rather than only an abstract quotient isomorphism. -/
theorem canonicalKOne (hR : IsPurelyInfiniteSimpleRing R)
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (matrixKappa R n) ∧
      (matrixKappa R n).ker = commutator (Matrix (Fin n) (Fin n) R)ˣ ∧
      mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ = (matrixKappa R n).ker ∧
      IsOperatorMF (AlgebraicKOne R) ∧
      (∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ f : (Matrix (Fin n) (Fin n) R)ˣ →* M,
          ∃! g : AlgebraicKOne R →* M, g.comp (matrixKappa R n) = f) :=
  ⟨matrixKappa_surjective R hR n hn, matrixKappa_ker R hR n hn,
    mfHomKernel_eq_matrixKappa_ker R hR n hn, countableAbelianMF _,
    fun M _ hM f => factors_uniquely_through_matrixKappa R hR n hn M hM f⟩

/-- The complete canonical classification as a closed manuscript statement. -/
def PrintedCanonicalKOne : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (n : ℕ), 1 ≤ n →
      Function.Surjective (matrixKappa R n) ∧
        (matrixKappa R n).ker = commutator (Matrix (Fin n) (Fin n) R)ˣ ∧
        mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ = (matrixKappa R n).ker ∧
        IsOperatorMF (AlgebraicKOne R) ∧
        (∀ (M : Type) [Group M], IsOperatorMF M →
          ∀ f : (Matrix (Fin n) (Fin n) R)ˣ →* M,
            ∃! g : AlgebraicKOne R →* M, g.comp (matrixKappa R n) = f)

theorem manuscriptCanonicalKOne : PrintedCanonicalKOne := by
  intro R _ _ hR n hn
  exact canonicalKOne R hR n hn

end MFQuotientUnitsKOne
end GroupApproximation

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptCanonicalKOne
#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOneAtBaseRing

#audit_axioms GroupApproximation.MFQuotientUnitsKOne.matrixMFQuotientEquiv_mk
