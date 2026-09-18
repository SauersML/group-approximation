import GroupApproximation.SteinbergFP.Diagonal
import GroupApproximation.Steinberg.ElementaryIndexPadding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Central
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Room: `K₂` is central after adjoining one index

For an index embedding `e : A ↪ B` the elementary matrix of `indexMap e g` is the identity
padding of the elementary matrix of `g` (`stMatrix_indexMap`), so `indexMap e` preserves and
reflects `K₂` (`stMatrix_indexMap_eq_one_iff`).

Adjoining one index makes `K₂` central: for `k ∈ K₂(A, S)` the image of `k` under
`A ↪ Option A` lies in the center of `St_{Option A}(S)` (`indexMap_some_mem_center`).  This is
Khanh's Lemma 5.2 (`LVCentral.castSuccStab_mem_center`), transported along
`Fin (|A| + 1) ≃ Option A`.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open SteinbergGroup ElementaryPadding

section Pad

variable {A B S : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Ring S]

/-- The elementary matrix of `indexMap e g` is the identity padding of that of `g`. -/
theorem stMatrix_indexMap (e : A ↪ B) (g : SteinbergGroup A S) :
    stMatrix B S (indexMap e g) = padHom e (stMatrix A S g) := by
  have h : (stMatrix B S).comp (indexMap (R := S) e) = (padHom e).comp (stMatrix A S) := by
    apply hom_ext_of_x
    intro a b hab r
    change stMatrix B S (indexMap e (x a b hab r)) = padHom e (stMatrix A S (x a b hab r))
    rw [indexMap_x, stMatrix_x, stMatrix_x, padHom_one_add_single]
  exact DFunLike.congr_fun h g

theorem padHom_apply_apply (e : A ↪ B) (M : Matrix A A S) (i j : A) :
    padHom e M (e i) (e j) = M i j := by
  have hi : (padEquiv e).symm (e i) = Sum.inl i := by
    rw [Equiv.symm_apply_eq, padEquiv_inl]
  have hj : (padEquiv e).symm (e j) = Sum.inl j := by
    rw [Equiv.symm_apply_eq, padEquiv_inl]
  rw [padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply, hi, hj,
    Matrix.fromBlocks_apply₁₁]

theorem padHom_injective (e : A ↪ B) : Function.Injective (padHom (R := S) e) := by
  intro M N h
  ext i j
  rw [← padHom_apply_apply e M i j, ← padHom_apply_apply e N i j, h]

/-- `indexMap e` preserves and reflects `K₂`. -/
theorem stMatrix_indexMap_eq_one_iff (e : A ↪ B) (g : SteinbergGroup A S) :
    stMatrix B S (indexMap e g) = 1 ↔ stMatrix A S g = 1 := by
  rw [stMatrix_indexMap, ← map_one (padHom (R := S) e)]
  exact (padHom_injective e).eq_iff

end Pad

section Reindex

variable {I J S : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Ring S]

theorem x_congr {i j i' j' : I} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j')
    (a : S) : x i j hij a = x i' j' hij' a := by
  subst hi
  subst hj
  rfl

theorem reindexEquiv_apply (e : I ≃ J) (g : SteinbergGroup I S) :
    reindexEquiv e g = indexMap e.toEmbedding g :=
  rfl

end Reindex

section Room

variable {A S : Type*} [Fintype A] [DecidableEq A] [Ring S]

/-- `Fin (m + 1) ≃ Option A`: `castSucc i ↦ some (α i)`, `last ↦ none`. -/
def optionFinEquiv {m : ℕ} (α : Fin m ≃ A) : Fin (m + 1) ≃ Option A :=
  finSuccEquivLast.trans (Equiv.optionCongr α)

omit [Fintype A] [DecidableEq A] in
theorem optionFinEquiv_castSucc {m : ℕ} (α : Fin m ≃ A) (i : Fin m) :
    optionFinEquiv α (Fin.castSucc i) = some (α i) := by
  simp [optionFinEquiv, finSuccEquivLast_castSucc]

/-- `A ↪ Option A` is stabilization, up to relabelling. -/
theorem indexMap_some_eq {m : ℕ} (α : Fin m ≃ A) (g : SteinbergGroup A S) :
    indexMap Function.Embedding.some g =
      reindexEquiv (optionFinEquiv α)
        (Full.LVCentral.castSuccStab m S (reindexEquiv α.symm g)) := by
  have h : indexMap (R := S) (Function.Embedding.some (α := A)) =
      (reindexEquiv (optionFinEquiv α)).toMonoidHom.comp
        ((Full.LVCentral.castSuccStab m S).comp (reindexEquiv (R := S) α.symm).toMonoidHom) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change indexMap _ (x i j hij a) = indexMap (optionFinEquiv α).toEmbedding
      (indexMap Fin.castSuccEmb (indexMap α.symm.toEmbedding (x i j hij a)))
    simp only [indexMap_x]
    apply x_congr
    · simp [optionFinEquiv_castSucc]
    · simp [optionFinEquiv_castSucc]
  exact DFunLike.congr_fun h g

/-- **Room lemma.** After adjoining one index, `K₂(A, S)` is central. -/
theorem indexMap_some_mem_center {g : SteinbergGroup A S} (hg : stMatrix A S g = 1) :
    indexMap Function.Embedding.some g ∈ Subgroup.center (SteinbergGroup (Option A) S) := by
  set α : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  have hk : reindexEquiv (R := S) α.symm g ∈
      (projection (I := Fin (Fintype.card A)) (R := S)).ker := by
    rw [MonoidHom.mem_ker, projection_eq_one_iff, reindexEquiv_apply,
      stMatrix_indexMap_eq_one_iff]
    exact hg
  have hc := Full.LVCentral.castSuccStab_mem_center hk
  rw [indexMap_some_eq α g, Subgroup.mem_center_iff]
  intro h
  obtain ⟨h', rfl⟩ := (reindexEquiv (R := S) (optionFinEquiv α)).surjective h
  have hh := congrArg (reindexEquiv (R := S) (optionFinEquiv α))
    (Subgroup.mem_center_iff.mp hc h')
  rwa [map_mul, map_mul] at hh

end Room

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.stMatrix_indexMap_eq_one_iff
#audit_axioms GroupApproximation.SteinbergFP.indexMap_some_mem_center
