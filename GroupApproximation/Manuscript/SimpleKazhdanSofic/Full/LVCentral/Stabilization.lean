import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Steinberg.ElementaryIndexPadding
import GroupApproximation.Steinberg.Functoriality

/-!
# Stabilization of Steinberg groups and padded vectors

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), cites Caprace--Rémy for infinite
finitely presented simple Kazhdan groups. On the Leavitt route to that claim the leaf T1b.ii of
the `K₂(4, L) = ⊥` tree is Khanh's Lemma 5.2 (arXiv:2609.08428; Lemma 5.6 in the foreign
`LeavittK2` code): the stabilization `St_m(B) → St_{m+1}(B)` sends `K₂(m, B)` into the centre.

This file sets up the ingredients:

* `castSuccStab m B : St_m(B) →* St_{m+1}(B)`, the relabelling along `Fin.castSucc`.
  It is definitionally `BooneHigman.SteinbergBasic.stab m B`.
* Stabilization is compatible with the projections to the elementary groups
  (`projection_castSuccStab`), so it maps `K₂(m, B)` into `K₂(m+1, B)` (`castSuccStab_mem_ker`).
* `padVec v`, which extends `v : Fin m → B` by a zero last coordinate. It is the coordinate vector
  of the column and row vectors in `LVCentral.Vectors`.

Everything here uses only modules wired into the library root.
-/

namespace GroupApproximation
namespace Full
namespace LVCentral

open SteinbergGroup ElementarySimplicity ElementaryPadding

/-- The stabilization `St_m(B) → St_{m+1}(B)` along `Fin.castSucc`
(`simple_kazhdan_sofic_group.tex` l.733-735, Khanh Lemma 5.2). -/
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

theorem projection_castSuccStab_eq_one {g : SteinbergGroup (Fin m) B} (hg : projection g = 1) :
    projection (castSuccStab m B g) = 1 := by
  rw [projection_castSuccStab, hg, map_one]

/-- Stabilization maps `K₂(m, B)` into `K₂(m+1, B)`. -/
theorem castSuccStab_mem_ker {g : SteinbergGroup (Fin m) B}
    (hg : g ∈ (projection (I := Fin m) (R := B)).ker) :
    castSuccStab m B g ∈ (projection (I := Fin (m + 1)) (R := B)).ker :=
  MonoidHom.mem_ker.mpr (projection_castSuccStab_eq_one (MonoidHom.mem_ker.mp hg))

/-! ### The underlying matrix -/

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
  | last => exact padVec_last 1
  | cast j => exact padVec_castSucc 1 j

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
      · subst hji
        rw [if_pos rfl, Pi.mulSingle_eq_same]
      · rw [if_neg (fun h => hji (Fin.castSucc_inj.mp h)), Pi.mulSingle_eq_of_ne hji, toAdd_one]

end LVCentral
end Full
end GroupApproximation
