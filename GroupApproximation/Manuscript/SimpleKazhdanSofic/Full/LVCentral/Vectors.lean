import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Tactic.Group
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Stabilization

/-!
# Column and row vectors in `St_{m+1}(B)`

Kervaire's column-vector argument, used for Khanh's Lemma 5.2 (arXiv:2609.08428; leaf T1b.ii of
the `K₂(4, L) = ⊥` tree behind `simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`).

* The column roots `x_{i,m}(a)`, `i < m`, commute pairwise, so they assemble into a homomorphism
  `colVec : (Fin m → B) → St_{m+1}(B)`. Its image in `E_{m+1}(B)` is `1 + colMatrix m v`, so
  `colVec` is injective modulo the projection (`colVec_eq_of_projection_eq`).
* Conjugation by a stabilized generator `x_{k,l}(b)` maps the range of `colVec` to itself
  (`colVec_conj_root`), hence so does conjugation by every stabilized element (`colVec_conj`).
* If `projection g = 1`, then `castSuccStab m B g` commutes with every column root
  (`commute_colRoot_of_projection_eq_one`).

The row roots `x_{m,j}(a)` give the same results (`rowVec`, `commute_rowRoot_of_projection_eq_one`).
-/

namespace GroupApproximation
namespace Full
namespace LVCentral

open SteinbergGroup ElementarySimplicity ElementaryPadding

variable {B : Type*} [Ring B] {m : ℕ}

/-! ### Column roots -/

/-- The column root `a ↦ x_{i,m}(a)` as a homomorphism from `Multiplicative B`. -/
def colRoot (i : Fin m) : Multiplicative B →* SteinbergGroup (Fin (m + 1)) B where
  toFun a := x i.castSucc (Fin.last m) (Fin.castSucc_ne_last i) a.toAdd
  map_one' := by simp only [toAdd_one, x_zero]
  map_mul' a b := by simp only [toAdd_mul, x_mul]

theorem colRoot_apply (i : Fin m) (a : Multiplicative B) :
    colRoot i a = x i.castSucc (Fin.last m) (Fin.castSucc_ne_last i) a.toAdd := rfl

theorem colRoot_commute :
    Pairwise fun i j : Fin m =>
      ∀ a b : Multiplicative B, Commute (colRoot i a) (colRoot j b) := by
  intro i j _ a b
  exact x_commute_of_ne i.castSucc (Fin.last m) j.castSucc (Fin.last m) (Fin.castSucc_ne_last i)
    (Fin.castSucc_ne_last j) (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last i).symm
    a.toAdd b.toAdd

/-- The column-vector homomorphism `v ↦ ∏ᵢ x_{i,m}(vᵢ)`. -/
def colVec : (Fin m → Multiplicative B) →* SteinbergGroup (Fin (m + 1)) B :=
  MonoidHom.noncommPiCoprod (N := fun _ : Fin m => Multiplicative B) colRoot colRoot_commute

theorem colVec_mulSingle (i : Fin m) (a : Multiplicative B) :
    colVec (Pi.mulSingle i a) = x i.castSucc (Fin.last m) (Fin.castSucc_ne_last i) a.toAdd :=
  (MonoidHom.noncommPiCoprod_mulSingle colRoot colRoot_commute i a).trans (colRoot_apply i a)

theorem elMat_projection_colVec (v : Fin m → Multiplicative B) :
    elMat (projection (colVec v)) = 1 + colMatrix (Fin.last m) (padVec v) := by
  induction v using Pi.mulSingle_induction with
  | one =>
      have hz : colMatrix (Fin.last m) (0 : Fin (m + 1) → B) = 0 :=
        colMatrix_eq_zero _ _ fun _ => rfl
      rw [map_one, map_one, elMat_one, padVec_one, hz, add_zero]
  | mul v w hv hw =>
      rw [map_mul, map_mul, elMat_mul, hv, hw, one_add_colMatrix_mul]
      refine congrArg
        (fun y => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) B) + colMatrix (Fin.last m) y) ?_
      funext r
      simp only [padVec_mul_apply, padVec_last, mul_zero, add_zero]
  | mulSingle i a =>
      rw [colVec_mulSingle, projection_x, elMat_elementaryRoot, single_eq_colMatrix]
      refine congrArg
        (fun y => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) B) + colMatrix (Fin.last m) y) ?_
      funext r
      exact padVec_mulSingle i a r

theorem colVec_eq_of_projection_eq {v w : Fin m → Multiplicative B}
    (h : projection (colVec v) = projection (colVec w)) : v = w := by
  have hmat := congrArg elMat h
  rw [elMat_projection_colVec, elMat_projection_colVec] at hmat
  funext j
  have hentry := congrFun (congrFun hmat j.castSucc) (Fin.last m)
  rw [Matrix.add_apply, Matrix.add_apply, colMatrix_apply, colMatrix_apply, if_pos rfl,
    if_pos rfl, padVec_castSucc, padVec_castSucc] at hentry
  exact Multiplicative.toAdd.injective (add_left_cancel hentry)

theorem colVec_conj_root (k l : Fin m) (hkl : k ≠ l) (b : B) (v : Fin m → Multiplicative B) :
    ∃ w, castSuccStab m B (x k l hkl b) * colVec v * (castSuccStab m B (x k l hkl b))⁻¹ =
      colVec w := by
  have hkl' : k.castSucc ≠ l.castSucc := fun h => hkl (Fin.castSucc_inj.mp h)
  rw [castSuccStab_x]
  induction v using Pi.mulSingle_induction with
  | one => exact ⟨1, by simp only [map_one, mul_one, mul_inv_cancel]⟩
  | mul v w hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      refine ⟨v' * w', ?_⟩
      rw [map_mul, map_mul, ← hv', ← hw']
      group
  | mulSingle i a =>
      by_cases hil : i = l
      · refine ⟨Pi.mulSingle k (Multiplicative.ofAdd (b * a.toAdd)) * Pi.mulSingle l a, ?_⟩
        rw [hil, map_mul]
        simp only [colVec_mulSingle, toAdd_ofAdd]
        rw [← x_commutator k.castSucc l.castSucc (Fin.last m) hkl' (Fin.castSucc_ne_last l)
          (Fin.castSucc_ne_last k) b a.toAdd, commutatorElement_def]
        group
      · refine ⟨Pi.mulSingle i a, ?_⟩
        rw [colVec_mulSingle]
        exact (x_commute_of_ne k.castSucc l.castSucc i.castSucc (Fin.last m) hkl'
          (Fin.castSucc_ne_last i) (fun h => hil (Fin.castSucc_inj.mp h).symm)
          (Fin.castSucc_ne_last k).symm b a.toAdd).mul_inv_cancel

theorem colVec_conj (g : SteinbergGroup (Fin m) B) (v : Fin m → Multiplicative B) :
    ∃ w, castSuccStab m B g * colVec v * (castSuccStab m B g)⁻¹ = colVec w := by
  have hg : g ∈ (Subgroup.normalizer (Set.range (colVec (m := m) (B := B)))).comap
      (castSuccStab m B) := by
    refine PresentedGroup.generated_by _ _ ?_ g
    rintro ⟨k, l, hkl, b⟩
    change castSuccStab m B (x k l hkl b) ∈
      Subgroup.normalizer (Set.range (colVec (m := m) (B := B)))
    rw [Subgroup.mem_set_normalizer_iff]
    intro u
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := colVec_conj_root k l hkl b v
      exact ⟨w, hw.symm⟩
    · rintro ⟨w, hw⟩
      obtain ⟨v, hv⟩ := colVec_conj_root k l hkl (-b) w
      refine ⟨v, ?_⟩
      rw [← hv, hw, x_neg, map_inv, inv_inv]
      group
  rw [Subgroup.mem_comap, Subgroup.mem_set_normalizer_iff] at hg
  obtain ⟨w, hw⟩ := (hg (colVec v)).mp ⟨v, rfl⟩
  exact ⟨w, hw.symm⟩

/-- A stabilized `K₂` element commutes with every column root `x_{i,m}(a)`. -/
theorem commute_colRoot_of_projection_eq_one {g : SteinbergGroup (Fin m) B}
    (hg : projection g = 1) (i : Fin m) (a : B) :
    Commute (castSuccStab m B g) (x i.castSucc (Fin.last m) (Fin.castSucc_ne_last i) a) := by
  obtain ⟨w, hw⟩ := colVec_conj g (Pi.mulSingle i (Multiplicative.ofAdd a))
  have hproj : projection (colVec (Pi.mulSingle i (Multiplicative.ofAdd a))) =
      projection (colVec w) := by
    rw [← hw, map_mul, map_mul, map_inv, projection_castSuccStab_eq_one hg, one_mul, inv_one,
      mul_one]
  rw [← colVec_eq_of_projection_eq hproj, colVec_mulSingle, toAdd_ofAdd] at hw
  exact mul_inv_eq_iff_eq_mul.mp hw

/-! ### Row roots -/

/-- The row root `a ↦ x_{m,j}(a)` as a homomorphism from `Multiplicative B`. -/
def rowRoot (j : Fin m) : Multiplicative B →* SteinbergGroup (Fin (m + 1)) B where
  toFun a := x (Fin.last m) j.castSucc (Fin.castSucc_ne_last j).symm a.toAdd
  map_one' := by simp only [toAdd_one, x_zero]
  map_mul' a b := by simp only [toAdd_mul, x_mul]

theorem rowRoot_apply (j : Fin m) (a : Multiplicative B) :
    rowRoot j a = x (Fin.last m) j.castSucc (Fin.castSucc_ne_last j).symm a.toAdd := rfl

theorem rowRoot_commute :
    Pairwise fun i j : Fin m =>
      ∀ a b : Multiplicative B, Commute (rowRoot i a) (rowRoot j b) := by
  intro i j _ a b
  exact x_commute_of_ne (Fin.last m) i.castSucc (Fin.last m) j.castSucc
    (Fin.castSucc_ne_last i).symm (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last i)
    (Fin.castSucc_ne_last j) a.toAdd b.toAdd

/-- The row-vector homomorphism `v ↦ ∏ⱼ x_{m,j}(vⱼ)`. -/
def rowVec : (Fin m → Multiplicative B) →* SteinbergGroup (Fin (m + 1)) B :=
  MonoidHom.noncommPiCoprod (N := fun _ : Fin m => Multiplicative B) rowRoot rowRoot_commute

theorem rowVec_mulSingle (j : Fin m) (a : Multiplicative B) :
    rowVec (Pi.mulSingle j a) = x (Fin.last m) j.castSucc (Fin.castSucc_ne_last j).symm a.toAdd :=
  (MonoidHom.noncommPiCoprod_mulSingle rowRoot rowRoot_commute j a).trans (rowRoot_apply j a)

theorem elMat_projection_rowVec (v : Fin m → Multiplicative B) :
    elMat (projection (rowVec v)) = 1 + rowMatrix (Fin.last m) (padVec v) := by
  induction v using Pi.mulSingle_induction with
  | one =>
      have hz : rowMatrix (Fin.last m) (0 : Fin (m + 1) → B) = 0 :=
        rowMatrix_eq_zero _ _ fun _ => rfl
      rw [map_one, map_one, elMat_one, padVec_one, hz, add_zero]
  | mul v w hv hw =>
      rw [map_mul, map_mul, elMat_mul, hv, hw, one_add_rowMatrix_mul]
      refine congrArg
        (fun y => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) B) + rowMatrix (Fin.last m) y) ?_
      funext r
      simp only [padVec_mul_apply, padVec_last, zero_mul, add_zero]
  | mulSingle j a =>
      rw [rowVec_mulSingle, projection_x, elMat_elementaryRoot, single_eq_rowMatrix]
      refine congrArg
        (fun y => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) B) + rowMatrix (Fin.last m) y) ?_
      funext r
      exact padVec_mulSingle j a r

theorem rowVec_eq_of_projection_eq {v w : Fin m → Multiplicative B}
    (h : projection (rowVec v) = projection (rowVec w)) : v = w := by
  have hmat := congrArg elMat h
  rw [elMat_projection_rowVec, elMat_projection_rowVec] at hmat
  funext j
  have hentry := congrFun (congrFun hmat (Fin.last m)) j.castSucc
  rw [Matrix.add_apply, Matrix.add_apply, rowMatrix_apply, rowMatrix_apply, if_pos rfl,
    if_pos rfl, padVec_castSucc, padVec_castSucc] at hentry
  exact Multiplicative.toAdd.injective (add_left_cancel hentry)

theorem rowVec_conj_root (k l : Fin m) (hkl : k ≠ l) (b : B) (v : Fin m → Multiplicative B) :
    ∃ w, castSuccStab m B (x k l hkl b) * rowVec v * (castSuccStab m B (x k l hkl b))⁻¹ =
      rowVec w := by
  have hkl' : k.castSucc ≠ l.castSucc := fun h => hkl (Fin.castSucc_inj.mp h)
  rw [castSuccStab_x]
  induction v using Pi.mulSingle_induction with
  | one => exact ⟨1, by simp only [map_one, mul_one, mul_inv_cancel]⟩
  | mul v w hv hw =>
      obtain ⟨v', hv'⟩ := hv
      obtain ⟨w', hw'⟩ := hw
      refine ⟨v' * w', ?_⟩
      rw [map_mul, map_mul, ← hv', ← hw']
      group
  | mulSingle j a =>
      by_cases hjk : j = k
      · refine ⟨Pi.mulSingle l (Multiplicative.ofAdd (-(a.toAdd * b))) * Pi.mulSingle k a, ?_⟩
        rw [hjk, map_mul]
        simp only [rowVec_mulSingle, toAdd_ofAdd]
        rw [x_neg, ← x_commutator (Fin.last m) k.castSucc l.castSucc
          (Fin.castSucc_ne_last k).symm hkl' (Fin.castSucc_ne_last l).symm a.toAdd b,
          commutatorElement_inv, commutatorElement_def]
        group
      · refine ⟨Pi.mulSingle j a, ?_⟩
        rw [rowVec_mulSingle]
        exact (x_commute_of_ne k.castSucc l.castSucc (Fin.last m) j.castSucc hkl'
          (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last l)
          (fun h => hjk (Fin.castSucc_inj.mp h)) b a.toAdd).mul_inv_cancel

theorem rowVec_conj (g : SteinbergGroup (Fin m) B) (v : Fin m → Multiplicative B) :
    ∃ w, castSuccStab m B g * rowVec v * (castSuccStab m B g)⁻¹ = rowVec w := by
  have hg : g ∈ (Subgroup.normalizer (Set.range (rowVec (m := m) (B := B)))).comap
      (castSuccStab m B) := by
    refine PresentedGroup.generated_by _ _ ?_ g
    rintro ⟨k, l, hkl, b⟩
    change castSuccStab m B (x k l hkl b) ∈
      Subgroup.normalizer (Set.range (rowVec (m := m) (B := B)))
    rw [Subgroup.mem_set_normalizer_iff]
    intro u
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, hw⟩ := rowVec_conj_root k l hkl b v
      exact ⟨w, hw.symm⟩
    · rintro ⟨w, hw⟩
      obtain ⟨v, hv⟩ := rowVec_conj_root k l hkl (-b) w
      refine ⟨v, ?_⟩
      rw [← hv, hw, x_neg, map_inv, inv_inv]
      group
  rw [Subgroup.mem_comap, Subgroup.mem_set_normalizer_iff] at hg
  obtain ⟨w, hw⟩ := (hg (rowVec v)).mp ⟨v, rfl⟩
  exact ⟨w, hw.symm⟩

/-- A stabilized `K₂` element commutes with every row root `x_{m,j}(a)`. -/
theorem commute_rowRoot_of_projection_eq_one {g : SteinbergGroup (Fin m) B}
    (hg : projection g = 1) (j : Fin m) (a : B) :
    Commute (castSuccStab m B g) (x (Fin.last m) j.castSucc (Fin.castSucc_ne_last j).symm a) := by
  obtain ⟨w, hw⟩ := rowVec_conj g (Pi.mulSingle j (Multiplicative.ofAdd a))
  have hproj : projection (rowVec (Pi.mulSingle j (Multiplicative.ofAdd a))) =
      projection (rowVec w) := by
    rw [← hw, map_mul, map_mul, map_inv, projection_castSuccStab_eq_one hg, one_mul, inv_one,
      mul_one]
  rw [← rowVec_eq_of_projection_eq hproj, rowVec_mulSingle, toAdd_ofAdd] at hw
  exact mul_inv_eq_iff_eq_mul.mp hw

end LVCentral
end Full
end GroupApproximation
