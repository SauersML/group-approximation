import GroupApproximation.Higman.CentralHNNFreeLabelAction
import GroupApproximation.GroupTheory.HNNBrittonSpelling

/-!
# Faithfulness of the central-HNN free-label action

In a central HNN extension both associated maps are the identity on the same
subgroup.  Consequently a stable crossing leaves the base coordinate fixed,
and the same right-coset transversal labels both signs.  Equality of adjacent
opposite labels is exactly a Britton pinch, so a reduced HNN spelling emits a
nonempty reduced free word.  This proves faithfulness without any finiteness
assumption on the base group.
-/

namespace GroupApproximation
namespace Higman
namespace CentralHNNFreeLabel

open HNNExtension

variable {G : Type} [Group G] (M : Subgroup G)

noncomputable section

noncomputable local instance labelDecidableEq
    (d : HNNExtension.NormalWord.TransversalPair G M M) : DecidableEq (Label M d) :=
  Classical.decEq _

/-- The base coordinate is unchanged by either signed stable crossing. -/
def crossBase (_u : ℤˣ) (x : G) : G := x

/-- Both signs read the same right-coset transversal. -/
def crossLabel (d : HNNExtension.NormalWord.TransversalPair G M M)
    (_u : ℤˣ) (x : G) : Label M d :=
  ((d.compl (1 : ℤˣ)).equiv x).2

/-- The Boolean convention used by `FreeGroup.mk`. -/
def crossSign (u : ℤˣ) : Bool := decide (u = 1)

omit [Group G] in
@[simp] theorem crossBase_apply (u : ℤˣ) (x : G) : crossBase u x = x := rfl

@[simp] theorem crossLabel_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M) (u : ℤˣ) (x : G) :
    crossLabel M d u x = ((d.compl (1 : ℤˣ)).equiv x).2 := rfl

@[simp] theorem crossSign_one : crossSign (1 : ℤˣ) = true := by
  simp [crossSign]

@[simp] theorem crossSign_neg_one : crossSign (-1 : ℤˣ) = false := by
  simp [crossSign]

/-- Opposite crossings emit the same label exactly at a Britton pinch. -/
theorem crossLabel_eq_iff_mem
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (u v : ℤˣ) (g x : G) :
    crossLabel M d u (g * crossBase v x) = crossLabel M d v x ↔ g ∈ M := by
  simpa only [crossBase_apply, crossLabel_apply] using
    FiniteHNNFreeLabelAction.source_transversal_eq_iff
      (A := M) (B := M) d g x

/-- First coordinate after running the stable syllables from right to left. -/
def baseRun : List (ℤˣ × G) → G → G
  | [], x => x
  | (u, g) :: l, x => crossBase u (g * baseRun l x)

/-- The signed free-label word emitted by the stable syllables. -/
def labelWord (d : HNNExtension.NormalWord.TransversalPair G M M) :
    List (ℤˣ × G) → G → List (Label M d × Bool)
  | [], _ => []
  | (u, g) :: l, x =>
      (crossLabel M d u (g * baseRun l x), crossSign u) :: labelWord d l x

@[simp] theorem baseRun_nil (x : G) : baseRun ([] : List (ℤˣ × G)) x = x := rfl

@[simp] theorem baseRun_cons
    (u : ℤˣ) (g : G) (l : List (ℤˣ × G)) (x : G) :
    baseRun ((u, g) :: l) x = crossBase u (g * baseRun l x) := rfl

@[simp] theorem labelWord_nil
    (d : HNNExtension.NormalWord.TransversalPair G M M) (x : G) :
    labelWord M d [] x = [] := rfl

@[simp] theorem labelWord_cons
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (u : ℤˣ) (g : G) (l : List (ℤˣ × G)) (x : G) :
    labelWord M d ((u, g) :: l) x =
      (crossLabel M d u (g * baseRun l x), crossSign u) :: labelWord M d l x := rfl

/-- A pinch-free seam forces equal signs whenever its labels agree. -/
theorem crossSign_eq_of_label_eq
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (u v : ℤˣ) (g x : G)
    (hseam : g ∈ HNNExtension.toSubgroup M M u → u = v)
    (hlabel : crossLabel M d u (g * crossBase v x) = crossLabel M d v x) :
    crossSign u = crossSign v := by
  by_cases huv : u = v
  · simp [huv]
  · have hmem : g ∈ M := (crossLabel_eq_iff_mem M d u v g x).1 hlabel
    exact absurd (hseam (by simpa [HNNExtension.toSubgroup] using hmem)) huv

/-- A pinch-free HNN spelling emits an already reduced free-group word. -/
theorem labelWord_isReduced
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    {l : List (ℤˣ × G)} (hl : HNNBritton.NoPinch M M l) (x : G) :
    FreeGroup.IsReduced (labelWord M d l x) := by
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
            apply crossSign_eq_of_label_eq M d u v g (h * baseRun l x)
            · exact fun hmem => hl.seam (v, h) (by simp) hmem
            · exact hlabel
          · exact ih hl.tail

theorem labelWord_ne_nil
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    {l : List (ℤˣ × G)} (hl : l ≠ []) (x : G) :
    labelWord M d l x ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons p l => simp [labelWord]

/-- A nonempty pinch-free spelling emits a nontrivial free-group element. -/
theorem mk_labelWord_ne_one
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    {l : List (ℤˣ × G)} (hne : l ≠ [])
    (hl : HNNBritton.NoPinch M M l) (x : G) :
    FreeGroup.mk (labelWord M d l x) ≠ 1 := by
  classical
  intro hone
  have hw : (FreeGroup.mk (labelWord M d l x)).toWord = [] :=
    FreeGroup.toWord_eq_nil_iff.mpr hone
  rw [FreeGroup.toWord_mk, (labelWord_isReduced M d hl x).reduce_eq] at hw
  exact labelWord_ne_nil M d hne x hw

/-- A signed stable crossing emits its one-letter free word. -/
theorem stablePerm_zpow_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (u : ℤˣ) (x : G) (w : FreeGroup (Label M d)) :
    ((stablePerm M d) ^ (u : ℤ)) (x, w) =
      (crossBase u x, FreeGroup.mk [(crossLabel M d u x, crossSign u)] * w) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
    rfl
  · change
      (x, (FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2)⁻¹ * w) =
        (x, FreeGroup.mk [(((d.compl (1 : ℤˣ)).equiv x).2, false)] * w)
    rw [FreeGroup.of, FreeGroup.inv_mk]
    rfl

/-- Exact evaluation of a headless Britton spelling. -/
theorem action_spell_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (l : List (ℤˣ × G)) (x : G) (w : FreeGroup (Label M d)) :
    action M d (HNNBritton.spell (MulEquiv.refl M) l) (x, w) =
      (baseRun l x, FreeGroup.mk (labelWord M d l x) * w) := by
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
        (crossLabel M d u (g * baseRun l x), crossSign u) :: labelWord M d l x =
          [(crossLabel M d u (g * baseRun l x), crossSign u)] ++ labelWord M d l x
        from rfl]
      rw [← FreeGroup.mul_mk]
      rw [mul_assoc]

/-- Evaluation of a full Britton word at the identity point. -/
theorem action_wordProd_one
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g : G) (l : List (ℤˣ × G)) :
    action M d (HNNBritton.wordProd (MulEquiv.refl M) g l)
        (1, (1 : FreeGroup (Label M d))) =
      (g * baseRun l 1, FreeGroup.mk (labelWord M d l 1)) := by
  rw [HNNBritton.wordProd, map_mul, Equiv.Perm.mul_apply, action_of,
    action_spell_apply, basePerm_apply]
  simp

/-- An element acting trivially is the identity. -/
theorem eq_one_of_action_eq_one
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    {z : CentHNN M} (hz : action M d z = 1) : z = 1 := by
  obtain ⟨g, l, hl, hprod⟩ := HNNBritton.exists_hasSpelling (MulEquiv.refl M) z
  have happ := DFunLike.congr_fun hz ((1 : G), (1 : FreeGroup (Label M d)))
  rw [← hprod, action_wordProd_one] at happ
  by_cases hnil : l = []
  · subst l
    have hg : g = 1 := by
      simpa [baseRun] using congrArg Prod.fst happ
    subst g
    simpa using hprod.symm
  · have hfree : FreeGroup.mk (labelWord M d l 1) = 1 := by
      simpa using congrArg Prod.snd happ
    exact absurd hfree (mk_labelWord_ne_one M d hnil hl 1)

/-- **The free-label action of a central HNN extension is faithful for every
base group.** -/
theorem action_injective
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    Function.Injective (action M d) := by
  refine (MonoidHom.ker_eq_bot_iff (action M d)).mp ?_
  apply le_antisymm
  · intro z hz
    have hz1 := eq_one_of_action_eq_one M d hz
    simp [hz1]
  · exact bot_le

/-! ## The kernel of the base retraction -/

/-- Retraction to the base group, killing the stable letter. -/
def baseRet : CentHNN M →* G :=
  HNNExtension.lift (MonoidHom.id G) 1 (by intro z; simp)

@[simp] theorem baseRet_of (g : G) : baseRet M (of g) = g := by
  simp [baseRet, HNNExtension.lift_of]

@[simp] theorem baseRet_t : baseRet M (t : CentHNN M) = 1 := by
  simp [baseRet, HNNExtension.lift_t]

/-- The first action coordinate is the left-regular action of `baseRet`. -/
theorem action_fst_apply
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (z : CentHNN M) (x : G) (w : FreeGroup (Label M d)) :
    (action M d z (x, w)).1 = baseRet M z * x := by
  induction z using HNNExtension.induction_on generalizing x w with
  | of g => simp
  | t => simp
  | mul a b ha hb =>
      rw [map_mul, Equiv.Perm.mul_apply, ha, hb, map_mul]
      group
  | inv a ha =>
      rw [map_inv, map_inv]
      let p := (action M d a)⁻¹ (x, w)
      have hp : action M d a p = (x, w) :=
        (action M d a).apply_symm_apply (x, w)
      change p.1 = (baseRet M a)⁻¹ * x
      calc
        p.1 = (baseRet M a)⁻¹ * (baseRet M a * p.1) := by group
        _ = (baseRet M a)⁻¹ * (action M d a (p.1, p.2)).1 := by
          rw [ha]
        _ = (baseRet M a)⁻¹ * x := by rw [show (p.1, p.2) = p from rfl, hp]

/-- It suffices for an element to fix the distinguished point in order to be
the identity. -/
theorem eq_one_of_action_apply_eq
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    {z : CentHNN M}
    (hz : action M d z ((1 : G), (1 : FreeGroup (Label M d))) = (1, 1)) :
    z = 1 := by
  obtain ⟨g, l, hl, hprod⟩ := HNNBritton.exists_hasSpelling (MulEquiv.refl M) z
  rw [← hprod, action_wordProd_one] at hz
  by_cases hnil : l = []
  · subst l
    have hg : g = 1 := by
      simpa [baseRun] using congrArg Prod.fst hz
    subst g
    simpa using hprod.symm
  · have hfree : FreeGroup.mk (labelWord M d l 1) = 1 := by
      simpa using congrArg Prod.snd hz
    exact absurd hfree (mk_labelWord_ne_one M d hnil hl 1)

/-- Equality at the distinguished point already detects equality in the
central HNN extension. -/
theorem eq_of_action_apply_eq
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    {x y : CentHNN M}
    (hxy : action M d x ((1 : G), (1 : FreeGroup (Label M d))) =
      action M d y ((1 : G), (1 : FreeGroup (Label M d)))) :
    x = y := by
  have hfix : action M d (y⁻¹ * x) ((1 : G), 1) = ((1 : G), 1) := by
    rw [map_mul, map_inv, Equiv.Perm.mul_apply, hxy]
    exact (action M d y).symm_apply_apply ((1 : G), 1)
  have hone : y⁻¹ * x = 1 := eq_one_of_action_apply_eq M d hfix
  have hyx : y = x := inv_mul_eq_one.mp hone
  exact hyx.symm

/-- A stable conjugate depends only on the right coset of its conjugator. -/
theorem stableConj_eq_conj_of_label_eq
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (q : Label M d) (s : G)
    (hs : ((d.compl (1 : ℤˣ)).equiv s).2 = q) :
    stableConj M d q = of s⁻¹ * (t : CentHNN M) * of s := by
  apply eq_of_action_apply_eq M d
  rw [action_stableConj_apply_one]
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply, action_of, action_t,
    basePerm_apply, basePerm_inv_apply, stablePerm_apply, mul_one]
  rw [hs]
  congr 1
  group

@[simp] theorem baseRet_stableConj
    (d : HNNExtension.NormalWord.TransversalPair G M M) (q : Label M d) :
    baseRet M (stableConj M d q) = 1 := by
  simp [stableConj]

theorem baseRet_comp_stableConjLift
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    (baseRet M).comp (stableConjLift M d) = 1 := by
  refine FreeGroup.ext_hom _ _ fun q => ?_
  simp [stableConjLift]

/-- **The kernel of the base retraction is exactly the free group on stable
conjugates indexed by the right cosets of `M`.** -/
theorem range_stableConjLift_eq_ker_baseRet
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    (stableConjLift M d).range = (baseRet M).ker := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      baseRet_comp_stableConjLift]
    rfl
  · intro z hz
    rw [MonoidHom.mem_ker] at hz
    let p : Space M d := action M d z ((1 : G), 1)
    let w : FreeGroup (Label M d) := p.2
    have hp : p = (1, w) := by
      apply Prod.ext
      · dsimp [p]
        rw [action_fst_apply, hz, one_mul]
      · rfl
    refine ⟨w, ?_⟩
    let y : CentHNN M := stableConjLift M d w
    have hy : action M d y ((1 : G), 1) = (1, w) := by
      exact action_stableConjLift_apply_one M d w
    have hpoint : action M d z ((1 : G), 1) = action M d y ((1 : G), 1) := by
      rw [show action M d z ((1 : G), 1) = p from rfl, hp, hy]
    have hfix :
        action M d (y⁻¹ * z) ((1 : G), 1) = ((1 : G), 1) := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, hpoint]
      exact (action M d y).symm_apply_apply ((1 : G), 1)
    have hone : y⁻¹ * z = 1 := eq_one_of_action_apply_eq M d hfix
    change y = z
    exact inv_mul_eq_one.mp hone

end

end CentralHNNFreeLabel
end Higman
end GroupApproximation
