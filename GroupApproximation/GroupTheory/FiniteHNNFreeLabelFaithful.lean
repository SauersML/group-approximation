import GroupApproximation.GroupTheory.FiniteHNNFreeLabelAction
import GroupApproximation.GroupTheory.HNNBrittonSpelling

/-!
# Faithfulness of the finite-base free-label HNN action

This file proves that the free-label action constructed in
`FiniteHNNFreeLabelAction` is faithful.  The central calculation is a seam
test: two consecutive stable crossings contribute inverse free letters with
the same label exactly when the intervening base syllable lies in the
associated subgroup.  Britton reducedness therefore makes the resulting
free-group word reduced and nonempty.
-/

namespace GroupApproximation
namespace FiniteHNNFreeLabelAction

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {A B : Subgroup G} (phi : A ≃* B)

open HNNExtension

noncomputable local instance labelDecidableEq
    (d : HNNExtension.NormalWord.TransversalPair G A B) : DecidableEq (Label d) :=
  Classical.decEq _

/-- The first-coordinate action of a signed stable crossing. -/
def crossBase (d : HNNExtension.NormalWord.TransversalPair G A B)
    (u : ℤˣ) (x : G) : G :=
  if u = 1 then baseIntertwiner phi d x else (baseIntertwiner phi d).symm x

/-- The source-transversal label emitted by a signed stable crossing. -/
def crossLabel (d : HNNExtension.NormalWord.TransversalPair G A B)
    (u : ℤˣ) (x : G) : Label d :=
  if u = 1 then ((d.compl (1 : ℤˣ)).equiv x).2
  else ((d.compl (1 : ℤˣ)).equiv ((baseIntertwiner phi d).symm x)).2

/-- The Boolean convention used by `FreeGroup.mk`: `true` is a positive
letter and `false` its inverse. -/
def crossSign (u : ℤˣ) : Bool := decide (u = 1)

@[simp] theorem crossBase_one
    (d : HNNExtension.NormalWord.TransversalPair G A B) (x : G) :
    crossBase phi d (1 : ℤˣ) x = baseIntertwiner phi d x := by
  simp [crossBase]

@[simp] theorem crossBase_neg_one
    (d : HNNExtension.NormalWord.TransversalPair G A B) (x : G) :
    crossBase phi d (-1 : ℤˣ) x = (baseIntertwiner phi d).symm x := by
  simp [crossBase]

@[simp] theorem crossLabel_one
    (d : HNNExtension.NormalWord.TransversalPair G A B) (x : G) :
    crossLabel phi d (1 : ℤˣ) x = ((d.compl (1 : ℤˣ)).equiv x).2 := by
  simp [crossLabel]

@[simp] theorem crossLabel_neg_one
    (d : HNNExtension.NormalWord.TransversalPair G A B) (x : G) :
    crossLabel phi d (-1 : ℤˣ) x =
      ((d.compl (1 : ℤˣ)).equiv ((baseIntertwiner phi d).symm x)).2 := by
  simp [crossLabel]

@[simp] theorem crossSign_one : crossSign (1 : ℤˣ) = true := by
  simp [crossSign]

@[simp] theorem crossSign_neg_one : crossSign (-1 : ℤˣ) = false := by
  simp [crossSign]

/-- Two opposite crossings emit the same free label exactly at a Britton
pinch.  This is the sole cancellation calculation needed below. -/
theorem crossLabel_eq_iff_mem_toSubgroup
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (u v : ℤˣ) (huv : u ≠ v) (g x : G) :
    crossLabel phi d u (g * crossBase phi d v x) = crossLabel phi d v x ↔
      g ∈ HNNExtension.toSubgroup A B u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl
  · exact absurd rfl huv
  · simpa only [crossLabel_one, crossBase_neg_one, crossLabel_neg_one,
        HNNExtension.toSubgroup_one] using
      source_transversal_eq_iff (A := A) (B := B) d g
        ((baseIntertwiner phi d).symm x)
  · rw [crossLabel_neg_one, crossBase_one, crossLabel_one,
      HNNExtension.toSubgroup_neg_one]
    constructor
    · intro hlabel
      have hmemA :
          (baseIntertwiner phi d).symm (g * baseIntertwiner phi d x) * x⁻¹ ∈ A := by
        have := (source_transversal_eq_iff (A := A) (B := B) d
          ((baseIntertwiner phi d).symm (g * baseIntertwiner phi d x) * x⁻¹) x).1
        apply this
        simpa [mul_assoc] using hlabel
      let a : A := ⟨(baseIntertwiner phi d).symm
        (g * baseIntertwiner phi d x) * x⁻¹, hmemA⟩
      have hV := baseIntertwiner_mul_left phi d a x
      have ha : (a : G) * x =
          (baseIntertwiner phi d).symm (g * baseIntertwiner phi d x) := by
        dsimp [a]
        group
      rw [ha, (baseIntertwiner phi d).apply_symm_apply] at hV
      have : ((phi a : B) : G) = g := by
        apply mul_right_cancel (b := baseIntertwiner phi d x)
        simpa using hV.symm
      rw [← this]
      exact (phi a).property
    · intro hgB
      let b : B := ⟨g, hgB⟩
      change ((d.compl (1 : ℤˣ)).equiv
          ((baseIntertwiner phi d).symm ((b : G) * baseIntertwiner phi d x))).2 =
        ((d.compl (1 : ℤˣ)).equiv x).2
      rw [baseIntertwiner_symm_mul_left phi d b (baseIntertwiner phi d x),
        (baseIntertwiner phi d).symm_apply_apply]
      exact source_transversal_mul_left d (phi.symm b) x
  · exact absurd rfl huv

/-! ## The free word emitted by a Britton spelling -/

/-- First coordinate after running the stable syllables from right to left. -/
def baseRun (phi : A ≃* B)
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    List (ℤˣ × G) → G → G
  | [], x => x
  | (u, g) :: l, x => crossBase phi d u (g * baseRun phi d l x)

/-- The signed free-label word emitted by the stable syllables. -/
def labelWord (phi : A ≃* B)
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    List (ℤˣ × G) → G → List (Label d × Bool)
  | [], _ => []
  | (u, g) :: l, x =>
      (crossLabel phi d u (g * baseRun phi d l x), crossSign u) ::
        labelWord phi d l x

@[simp] theorem baseRun_nil
    (d : HNNExtension.NormalWord.TransversalPair G A B) (x : G) :
    baseRun phi d [] x = x := rfl

@[simp] theorem baseRun_cons
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (u : ℤˣ) (g : G) (l : List (ℤˣ × G)) (x : G) :
    baseRun phi d ((u, g) :: l) x =
      crossBase phi d u (g * baseRun phi d l x) := rfl

@[simp] theorem labelWord_nil
    (d : HNNExtension.NormalWord.TransversalPair G A B) (x : G) :
    labelWord phi d [] x = [] := rfl

@[simp] theorem labelWord_cons
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (u : ℤˣ) (g : G) (l : List (ℤˣ × G)) (x : G) :
    labelWord phi d ((u, g) :: l) x =
      (crossLabel phi d u (g * baseRun phi d l x), crossSign u) ::
        labelWord phi d l x := rfl

/-- A Britton seam forces equal signs whenever its two emitted free labels
agree. -/
theorem crossSign_eq_of_label_eq
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (u v : ℤˣ) (g x : G)
    (hseam : g ∈ HNNExtension.toSubgroup A B u → u = v)
    (hlabel : crossLabel phi d u (g * crossBase phi d v x) =
      crossLabel phi d v x) :
    crossSign u = crossSign v := by
  by_cases huv : u = v
  · simp [huv]
  · have hmem :=
      (crossLabel_eq_iff_mem_toSubgroup phi d u v huv g x).1 hlabel
    exact absurd (hseam hmem) huv

/-- A pinch-free HNN spelling emits an already reduced free-group word. -/
theorem labelWord_isReduced
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    {l : List (ℤˣ × G)} (hl : HNNBritton.NoPinch A B l) (x : G) :
    FreeGroup.IsReduced (labelWord phi d l x) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons p l ih =>
      rcases p with ⟨u, g⟩
      cases l with
      | nil => exact List.isChain_singleton _
      | cons q l =>
          rcases q with ⟨v, h⟩
          apply List.isChain_cons_cons.2
          constructor
          · intro hlabel
            apply crossSign_eq_of_label_eq phi d u v g
              (h * baseRun phi d l x)
            · exact fun hmem => hl.seam (v, h) (by simp) hmem
            · exact hlabel
          · exact ih hl.tail

/-- A nonempty HNN syllable list emits a nonempty label list. -/
theorem labelWord_ne_nil
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    {l : List (ℤˣ × G)} (hl : l ≠ []) (x : G) :
    labelWord phi d l x ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons p l => simp [labelWord]

/-- The free group element represented by a nonempty pinch-free spelling is
nontrivial. -/
theorem mk_labelWord_ne_one
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    {l : List (ℤˣ × G)} (hne : l ≠ [])
    (hl : HNNBritton.NoPinch A B l) (x : G) :
    FreeGroup.mk (labelWord phi d l x) ≠ 1 := by
  classical
  intro hone
  have hw : (FreeGroup.mk (labelWord phi d l x)).toWord = [] :=
    FreeGroup.toWord_eq_nil_iff.mpr hone
  rw [FreeGroup.toWord_mk, (labelWord_isReduced phi d hl x).reduce_eq] at hw
  exact labelWord_ne_nil phi d hne x hw

/-! ## Evaluation and faithfulness -/

/-- A signed stable crossing emits the corresponding one-letter free word. -/
theorem stablePerm_zpow_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (u : ℤˣ) (x : G) (w : FreeGroup (Label d)) :
    ((stablePerm phi d) ^ (u : ℤ)) (x, w) =
      (crossBase phi d u x,
        FreeGroup.mk [(crossLabel phi d u x, crossSign u)] * w) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
    rfl
  · simp
    rw [FreeGroup.of, FreeGroup.inv_mk]
    rfl

/-- Exact evaluation of the headless Britton spelling under the free-label
action. -/
theorem action_spell_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (l : List (ℤˣ × G)) (x : G) (w : FreeGroup (Label d)) :
    action phi d (HNNBritton.spell phi l) (x, w) =
      (baseRun phi d l x, FreeGroup.mk (labelWord phi d l x) * w) := by
  induction l with
  | nil =>
      change (x, w) = (x, FreeGroup.mk [] * w)
      rw [← FreeGroup.one_eq_mk, one_mul]
  | cons p l ih =>
      rcases p with ⟨u, g⟩
      rw [HNNBritton.spell_cons]
      simp only [map_mul, Equiv.Perm.mul_apply, action_t, action_of, map_zpow,
        basePerm_apply, ih, stablePerm_zpow_apply, baseRun_cons, labelWord_cons]
      rw [show
        (crossLabel phi d u (g * baseRun phi d l x), crossSign u) ::
            labelWord phi d l x =
          [(crossLabel phi d u (g * baseRun phi d l x), crossSign u)] ++
            labelWord phi d l x from rfl]
      rw [← FreeGroup.mul_mk]
      rw [mul_assoc]

/-- Evaluation of a full Britton word at the identity point. -/
theorem action_wordProd_one
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (g : G) (l : List (ℤˣ × G)) :
    action phi d (HNNBritton.wordProd phi g l)
        (1, (1 : FreeGroup (Label d))) =
      (g * baseRun phi d l 1, FreeGroup.mk (labelWord phi d l 1)) := by
  rw [HNNBritton.wordProd, map_mul, Equiv.Perm.mul_apply, action_of,
    action_spell_apply, basePerm_apply]
  simp

/-- An element acting trivially in the free-label model is the identity. -/
theorem eq_one_of_action_eq_one
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    {z : HNNExtension G A B phi} (hz : action phi d z = 1) : z = 1 := by
  obtain ⟨g, l, hl, hprod⟩ := HNNBritton.exists_hasSpelling phi z
  have happ := DFunLike.congr_fun hz ((1 : G), (1 : FreeGroup (Label d)))
  rw [← hprod, action_wordProd_one] at happ
  by_cases hnil : l = []
  · subst l
    have hg : g = 1 := by
      simpa [baseRun] using congrArg Prod.fst happ
    subst g
    simpa using hprod.symm
  · have hfree : FreeGroup.mk (labelWord phi d l 1) = 1 := by
      simpa using congrArg Prod.snd happ
    exact absurd hfree (mk_labelWord_ne_one phi d hnil hl 1)

/-- The free-label permutation action of a finite-base HNN extension is
faithful. -/
theorem action_injective
    (d : HNNExtension.NormalWord.TransversalPair G A B) :
    Function.Injective (action phi d) := by
  refine (MonoidHom.ker_eq_bot_iff (action phi d)).mp ?_
  apply le_antisymm
  · intro z hz
    have hz1 := eq_one_of_action_eq_one phi d hz
    simp [hz1]
  · exact bot_le

end

end FiniteHNNFreeLabelAction
end GroupApproximation
