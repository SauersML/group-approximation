import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Tactic.Group
import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Steinberg.ElementaryIndexPadding
import GroupApproximation.Steinberg.Functoriality

/-!
# Stabilized `K₂` is central one rank up

The manuscript's question section (`simple_kazhdan_sofic_group.tex`, l.733-734, `sec:questions`)
cites Caprace--Rémy for infinite finitely presented simple Kazhdan groups. The Leavitt route to
that claim reduces to finite normal generation of `K₂(4, L)` for the binary Leavitt algebra `L`.
Khanh's proof (arXiv:2609.08428, Theorem 5.1) relies on Lemma 5.2: for any ring `B`, the
stabilization `j_m : St_m(B) → St_{m+1}(B)` sends `K₂(m, B)` into the centre of `St_{m+1}(B)`.
This file proves that lemma unconditionally. It is leaf T1b.ii of the SK17 lemma tree.

The proof is Kervaire's column-vector argument.

* The column roots `x_{i,m}(a)`, `i < m`, commute pairwise, so they assemble into a homomorphism
  `colVec : (Fin m → B) → St_{m+1}(B)`. Its image in `EL_{m+1}(B)` is `1 + colMatrix m v`, so
  `colVec` is injective modulo the projection (`colVec_eq_of_projection_eq`).
* Conjugation by a stabilized generator `x_{k,l}(b)` maps the range of `colVec` to itself
  (`colVec_conj_root`), hence so does conjugation by every stabilized element (`colVec_conj`).
* If `g ∈ K₂(m, B)`, then conjugating `colVec v` by `j_m g` gives some `colVec w` with the same
  projection, so `w = v`. Hence `j_m g` commutes with all column roots, and likewise with all
  row roots `x_{m,j}(a)`.
* Every other generator is a commutator `x_{i,j}(a) = ⁅x_{i,m}(a), x_{m,j}(1)⁆`, so `j_m g`
  commutes with all generators and is central (`map_ker_projection_le_center`).
-/

namespace GroupApproximation
namespace Full
namespace SK17

open scoped commutatorElement
open SteinbergGroup ElementarySimplicity ElementaryPadding

/-- The stabilization `St_m(B) → St_{m+1}(B)` along `Fin.castSucc`. -/
abbrev castSuccStab (m : ℕ) (B : Type*) [Ring B] :
    SteinbergGroup (Fin m) B →* SteinbergGroup (Fin (m + 1)) B :=
  SteinbergGroup.indexMap Fin.castSuccEmb

variable {B : Type*} [Ring B] {m : ℕ}

theorem castSuccStab_x (k l : Fin m) (hkl : k ≠ l) (b : B) :
    castSuccStab m B (x k l hkl b) =
      x k.castSucc l.castSucc (fun h => hkl (Fin.castSucc_inj.mp h)) b :=
  indexMap_x _ k l hkl b

/-- Stabilization is compatible with the projections to the elementary groups. -/
theorem projection_castSuccStab (u : SteinbergGroup (Fin m) B) :
    projection (castSuccStab m B u) = elementaryPad Fin.castSuccEmb (projection u) := by
  have h : (projection (I := Fin (m + 1)) (R := B)).comp (castSuccStab m B) =
      (elementaryPad Fin.castSuccEmb).comp (projection (I := Fin m) (R := B)) := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, a⟩
    change projection (SteinbergGroup.indexMap Fin.castSuccEmb (x i j hij a)) =
      elementaryPad Fin.castSuccEmb (projection (x i j hij a))
    rw [indexMap_x, projection_x, projection_x, elementaryPad_elementaryRoot]
  exact DFunLike.congr_fun h u

/-! ### The underlying matrix -/

theorem elMat_one_eq {ι : Type*} [Fintype ι] [DecidableEq ι] :
    elMat (1 : elementaryGroup ι B) = 1 := rfl

theorem elMat_elementaryRoot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (a : B) :
    elMat (elementaryRoot i j hij a) = 1 + Matrix.single i j a := rfl

/-- Extend a vector indexed by `Fin m` by a zero last coordinate. -/
def padVec (v : Fin m → Multiplicative B) : Fin (m + 1) → B :=
  fun r => Fin.lastCases (motive := fun _ => B) 0 (fun j => (v j).toAdd) r

@[simp] theorem padVec_last (v : Fin m → Multiplicative B) : padVec v (Fin.last m) = 0 := by
  simp only [padVec, Fin.lastCases_last]

@[simp] theorem padVec_castSucc (v : Fin m → Multiplicative B) (j : Fin m) :
    padVec v j.castSucc = (v j).toAdd := by
  simp only [padVec, Fin.lastCases_castSucc]

theorem padVec_one : padVec (1 : Fin m → Multiplicative B) = 0 := by
  funext r
  induction r using Fin.lastCases with
  | last => rw [padVec_last, Pi.zero_apply]
  | cast j => rw [padVec_castSucc, Pi.one_apply, toAdd_one, Pi.zero_apply]

theorem padVec_mul_apply (v w : Fin m → Multiplicative B) (r : Fin (m + 1)) :
    padVec (v * w) r = padVec v r + padVec w r := by
  induction r using Fin.lastCases with
  | last => rw [padVec_last, padVec_last, padVec_last, add_zero]
  | cast j => rw [padVec_castSucc, padVec_castSucc, padVec_castSucc, Pi.mul_apply, toAdd_mul]

theorem padVec_mulSingle (i : Fin m) (a : Multiplicative B) (r : Fin (m + 1)) :
    (if r = i.castSucc then a.toAdd else 0) = padVec (Pi.mulSingle i a) r := by
  induction r using Fin.lastCases with
  | last => rw [if_neg (Fin.castSucc_ne_last i).symm, padVec_last]
  | cast j =>
      rw [padVec_castSucc]
      by_cases hji : j = i
      · rw [hji, if_pos rfl, Pi.mulSingle_eq_same]
      · rw [if_neg (fun h => hji (Fin.castSucc_inj.mp h)), Pi.mulSingle_eq_of_ne hji, toAdd_one]

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
      rw [map_one, map_one, elMat_one_eq, padVec_one, hz, add_zero]
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
  | one => exact ⟨1, by rw [map_one, mul_one, mul_inv_cancel]⟩
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

theorem projection_castSuccStab_eq_one {g : SteinbergGroup (Fin m) B} (hg : projection g = 1) :
    projection (castSuccStab m B g) = 1 := by
  rw [projection_castSuccStab, hg, map_one]

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
      rw [map_one, map_one, elMat_one_eq, padVec_one, hz, add_zero]
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
  | one => exact ⟨1, by rw [map_one, mul_one, mul_inv_cancel]⟩
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

/-! ### Centrality -/

theorem commute_x_of_projection_eq_one {g : SteinbergGroup (Fin m) B} (hg : projection g = 1)
    (p q : Fin (m + 1)) (hpq : p ≠ q) (a : B) :
    Commute (castSuccStab m B g) (x p q hpq a) := by
  induction p using Fin.lastCases with
  | last =>
      induction q using Fin.lastCases with
      | last => exact (hpq rfl).elim
      | cast j => exact commute_rowRoot_of_projection_eq_one hg j a
  | cast i =>
      induction q using Fin.lastCases with
      | last => exact commute_colRoot_of_projection_eq_one hg i a
      | cast j =>
          have hc := commute_colRoot_of_projection_eq_one hg i a
          have hr := commute_rowRoot_of_projection_eq_one hg j 1
          have hcomm := x_commutator i.castSucc (Fin.last m) j.castSucc
            (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j).symm hpq a 1
          rw [mul_one] at hcomm
          rw [← hcomm, commutatorElement_def]
          exact ((hc.mul_right hr).mul_right hc.inv_right).mul_right hr.inv_right

/-- Khanh, Lemma 5.2: a stabilized `K₂` element is central one rank up. -/
theorem castSuccStab_mem_center {g : SteinbergGroup (Fin m) B}
    (hg : g ∈ (projection (I := Fin m) (R := B)).ker) :
    castSuccStab m B g ∈ Subgroup.center (SteinbergGroup (Fin (m + 1)) B) := by
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_center_iff]
  intro h
  have hh : h ∈ Subgroup.centralizer {castSuccStab m B g} := by
    refine PresentedGroup.generated_by _ _ ?_ h
    rintro ⟨p, q, hpq, a⟩
    change x p q hpq a ∈ Subgroup.centralizer {castSuccStab m B g}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_x_of_projection_eq_one hg p q hpq a).symm
  rw [Subgroup.mem_centralizer_singleton_iff] at hh
  exact hh

/-- The image of `K₂(m, B)` under stabilization lies in the centre of `St_{m+1}(B)`. -/
theorem map_ker_projection_le_center :
    (projection (I := Fin m) (R := B)).ker.map (castSuccStab m B) ≤
      Subgroup.center (SteinbergGroup (Fin (m + 1)) B) := by
  rintro _ ⟨g, hg, rfl⟩
  exact castSuccStab_mem_center hg

end SK17
end Full
end GroupApproximation
