import GroupApproximation.Sofic.CliffordLampGraphLocalFiniteness
import Mathlib.GroupTheory.CoprodI
import Mathlib.Algebra.Group.Commutator

/-!
# Three blocks give a nonabelian free subgroup of `C(𝒢)`

`Sofic.CliffordLampGraphLocalFiniteness` proves the first half of the
manuscript's sentence about the lamp factor of the orbital graph:

> `C(𝒢)` is not locally finite, since two lamps at sites of different blocks
> generate an infinite dihedral group and three blocks give a nonabelian free
> subgroup.

The infinite dihedral half is `not_isLocallyFiniteGroup_lampFactor`, whose
witness sends two non-adjacent lamps to the two reflections of
`DihedralGroup 0`.  This module proves the *second* half: three pairwise
non-adjacent sites -- in particular three sites in three distinct blocks, since
`blockOf_eq_of_adjacent` makes adjacent sites share a block -- carry lamps
whose products generate a free group of rank two inside `C(𝒢)`.

## The witness

The presentation `IsLampRelator` imposes a braiding relation only along the
edges of `𝒢`; between pairwise non-adjacent sites it imposes nothing beyond
the involutivity of each lamp.  So three such lamps may be sent to any three
involutions whatsoever, and the sign `ζ` to `1`.  We send them to the three
*letter flips* of the reduced words on three letters:

`RedWord` is the set of finite words over `Fin 3` with no two adjacent letters
equal, and `letterFlip i` deletes a leading `i` when there is one and prepends
an `i` otherwise.  Reducedness is exactly what makes `letterFlip i` an
involution: after deleting a leading `i` the new first letter is not `i`, so
the second application puts it back.

These are the three generating reflections of the Bass--Serre tree of
`ℤ/2 ∗ ℤ/2 ∗ ℤ/2`, written out as an elementary list construction so that no
free-product normal-form theory is needed.  Each `letterFlip i` carries the
complement of `startSet i` -- the words that do *not* begin with `i` -- into
`startSet i`, and the three `startSet i` are pairwise disjoint.  That is
precisely the input of mathlib's ping-pong lemma for the two elements

`x = letterFlip 0 * letterFlip 1`,  `y = letterFlip 0 * letterFlip 2`,

with ping-pong sets `X₀ = σ₀ • S₁`, `X₁ = σ₀ • S₂`, `Y₀ = S₁`, `Y₁ = S₂`.

## What is proved

* `lampFreePair_lift_injective` -- `FreeGroup (Fin 2) → C(𝒢)` sending the two
  free generators to `c_ξc_η` and `c_ξc_θ` is **injective**;
* `exists_free_subgroup_of_three_nonadjacent` and
  `exists_free_subgroup_of_three_blocks` -- the printed sentence: a subgroup of
  `C(𝒢)` isomorphic to the free group of rank two;
* `lampFreePair_not_commute` -- that subgroup is nonabelian, so "nonabelian
  free subgroup" is proved and not merely "free subgroup".

Nothing here is conditional: the hypotheses are the geometric ones the
manuscript's own sentence carries (three sites, three distinct blocks), and
`LiteralBlockNormalForm` supplies `blockOf_eq_of_adjacent` outright.
-/

namespace GroupApproximation
namespace CliffordLampGraph

open LiteralBlockNormalForm
open scoped Pointwise
open scoped commutatorElement
-- `open scoped` alone does not put the commutator instance into resolution
-- here; the bracket below needs it as an instance.
attribute [local instance] commutatorElement

/-! ## Reduced words on three letters -/

/-- Words over three letters with no two adjacent letters equal. -/
inductive ReducedWord : List (Fin 3) → Prop
  | nil : ReducedWord []
  | singleton (i : Fin 3) : ReducedWord [i]
  | cons {i j : Fin 3} {l : List (Fin 3)} (h : i ≠ j)
      (hr : ReducedWord (j :: l)) : ReducedWord (i :: j :: l)

theorem ReducedWord.of_cons {a : Fin 3} {t : List (Fin 3)}
    (h : ReducedWord (a :: t)) : ReducedWord t := by
  cases h with
  | singleton _ => exact ReducedWord.nil
  | cons _ hr => exact hr

theorem ReducedWord.head_ne {a b : Fin 3} {t : List (Fin 3)}
    (h : ReducedWord (a :: b :: t)) : a ≠ b := by
  cases h with
  | cons hne _ => exact hne

/-- The carrier of the ping-pong action: reduced words on three letters. -/
abbrev RedWord : Type := {w : List (Fin 3) // ReducedWord w}

/-- Delete a leading `i` if there is one, otherwise prepend an `i`. -/
def flipWord (i : Fin 3) (w : List (Fin 3)) : List (Fin 3) :=
  match w with
  | [] => [i]
  | a :: t => if a = i then t else i :: a :: t

theorem flipWord_nil (i : Fin 3) : flipWord i [] = [i] := rfl

theorem flipWord_cons (i a : Fin 3) (t : List (Fin 3)) :
    flipWord i (a :: t) = if a = i then t else i :: a :: t := rfl

theorem flipWord_cons_self (i : Fin 3) (t : List (Fin 3)) :
    flipWord i (i :: t) = t := by
  rw [flipWord_cons, if_pos rfl]

theorem flipWord_cons_ne {i a : Fin 3} (h : a ≠ i) (t : List (Fin 3)) :
    flipWord i (a :: t) = i :: a :: t := by
  rw [flipWord_cons, if_neg h]

theorem reducedWord_flipWord (i : Fin 3) {w : List (Fin 3)}
    (h : ReducedWord w) : ReducedWord (flipWord i w) := by
  cases w with
  | nil => exact ReducedWord.singleton i
  | cons a t =>
      by_cases hai : a = i
      · rw [flipWord_cons, if_pos hai]
        exact h.of_cons
      · rw [flipWord_cons, if_neg hai]
        exact ReducedWord.cons (fun hia => hai hia.symm) h

theorem flipWord_flipWord (i : Fin 3) {w : List (Fin 3)}
    (h : ReducedWord w) : flipWord i (flipWord i w) = w := by
  cases w with
  | nil =>
      rw [flipWord_nil, flipWord_cons_self]
  | cons a t =>
      by_cases hai : a = i
      · have h1 : flipWord i (a :: t) = t := by rw [flipWord_cons, if_pos hai]
        rw [h1]
        cases t with
        | nil => rw [flipWord_nil, hai]
        | cons b t' =>
            have hab : a ≠ b := h.head_ne
            have hbi : b ≠ i := fun hb => hab (hai.trans hb.symm)
            rw [flipWord_cons_ne hbi, hai]
      · have h1 : flipWord i (a :: t) = i :: a :: t := by
          rw [flipWord_cons, if_neg hai]
        rw [h1, flipWord_cons_self]

/-- The letter-`i` flip, as a permutation of the reduced words. -/
def letterFlip (i : Fin 3) : Equiv.Perm RedWord where
  toFun w := ⟨flipWord i w.1, reducedWord_flipWord i w.2⟩
  invFun w := ⟨flipWord i w.1, reducedWord_flipWord i w.2⟩
  left_inv w := Subtype.ext (flipWord_flipWord i w.2)
  right_inv w := Subtype.ext (flipWord_flipWord i w.2)

theorem letterFlip_val (i : Fin 3) (w : RedWord) :
    (letterFlip i w).1 = flipWord i w.1 := rfl

/-- Each letter flip is an involution: this is where reducedness is used. -/
theorem letterFlip_mul_self (i : Fin 3) : letterFlip i * letterFlip i = 1 :=
  Equiv.ext fun w => Subtype.ext (flipWord_flipWord i w.2)

theorem letterFlip_inv (i : Fin 3) : (letterFlip i)⁻¹ = letterFlip i :=
  inv_eq_of_mul_eq_one_right (letterFlip_mul_self i)

/-! ## The ping-pong sets -/

/-- The reduced words that begin with the letter `i`. -/
def startSet (i : Fin 3) : Set RedWord := {w : RedWord | w.1.head? = some i}

theorem startSet_nonempty (i : Fin 3) : (startSet i).Nonempty :=
  ⟨⟨[i], ReducedWord.singleton i⟩, rfl⟩

theorem startSet_disjoint {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (startSet i) (startSet j) := by
  refine Set.disjoint_left.mpr ?_
  intro w hwi hwj
  have hi : w.1.head? = some i := hwi
  have hj : w.1.head? = some j := hwj
  exact hij (Option.some_inj.mp (hi.symm.trans hj))

theorem head?_flipWord_of_ne {i : Fin 3} {l : List (Fin 3)}
    (h : l.head? ≠ some i) : (flipWord i l).head? = some i := by
  cases l with
  | nil => rfl
  | cons a t =>
      have hai : a ≠ i := by
        intro hh
        subst hh
        exact h rfl
      exact (congrArg List.head? (flipWord_cons_ne hai t)).trans rfl

theorem letterFlip_mem_startSet {i : Fin 3} {w : RedWord}
    (hw : w ∉ startSet i) : letterFlip i w ∈ startSet i := by
  have hw' : w.1.head? ≠ some i := hw
  show (flipWord i w.1).head? = some i
  exact head?_flipWord_of_ne hw'

/-- **The ping-pong estimate.**  Each letter flip carries the complement of its
own start set inside that start set. -/
theorem letterFlip_smul_compl_subset (i : Fin 3) :
    letterFlip i • (startSet i)ᶜ ⊆ startSet i := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact letterFlip_mem_startSet hw

/-! ## The two free generators -/

/-- The two elements the ping-pong lemma is applied to. -/
def pingGen : Fin 2 → Equiv.Perm RedWord
  | 0 => letterFlip 0 * letterFlip 1
  | 1 => letterFlip 0 * letterFlip 2

/-- The attracting sets. -/
def pingX : Fin 2 → Set RedWord
  | 0 => letterFlip 0 • startSet 1
  | 1 => letterFlip 0 • startSet 2

/-- The repelling sets. -/
def pingY : Fin 2 → Set RedWord
  | 0 => startSet 1
  | 1 => startSet 2

theorem pingX_nonempty : ∀ i, (pingX i).Nonempty := by
  intro i
  match i with
  | 0 =>
      obtain ⟨w, hw⟩ := startSet_nonempty 1
      exact ⟨letterFlip 0 • w, Set.smul_mem_smul_set hw⟩
  | 1 =>
      obtain ⟨w, hw⟩ := startSet_nonempty 2
      exact ⟨letterFlip 0 • w, Set.smul_mem_smul_set hw⟩

theorem smul_startSet_disjoint {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (letterFlip 0 • startSet i) (letterFlip 0 • startSet j) := by
  refine Set.disjoint_left.mpr ?_
  intro x hx1 hx2
  obtain ⟨w, hw, rfl⟩ := hx1
  rw [Set.smul_mem_smul_set_iff] at hx2
  exact Set.disjoint_left.mp (startSet_disjoint hij) hw hx2

theorem pingX_disjoint : Pairwise (Function.onFun Disjoint pingX) := by
  intro i j hij
  match i, j, hij with
  | 0, 0, hij => exact absurd rfl hij
  | 1, 1, hij => exact absurd rfl hij
  | 0, 1, _ => exact smul_startSet_disjoint (i := 1) (j := 2) (by decide)
  | 1, 0, _ => exact smul_startSet_disjoint (i := 2) (j := 1) (by decide)

theorem pingY_disjoint : Pairwise (Function.onFun Disjoint pingY) := by
  intro i j hij
  match i, j, hij with
  | 0, 0, hij => exact absurd rfl hij
  | 1, 1, hij => exact absurd rfl hij
  | 0, 1, _ => exact startSet_disjoint (i := 1) (j := 2) (by decide)
  | 1, 0, _ => exact startSet_disjoint (i := 2) (j := 1) (by decide)

theorem smul_startSet_subset_zero {k : Fin 3} (hk : k ≠ 0) :
    letterFlip 0 • startSet k ⊆ startSet 0 := by
  have h1 : startSet k ⊆ (startSet 0)ᶜ := by
    intro w hw hw0
    exact Set.disjoint_left.mp (startSet_disjoint (Ne.symm hk)) hw0 hw
  exact (Set.smul_set_mono h1).trans (letterFlip_smul_compl_subset 0)

theorem pingXY_disjoint : ∀ i j, Disjoint (pingX i) (pingY j) := by
  intro i j
  match i, j with
  | 0, 0 =>
      exact (startSet_disjoint (i := 0) (j := 1) (by decide)).mono_left
        (smul_startSet_subset_zero (k := 1) (by decide))
  | 0, 1 =>
      exact (startSet_disjoint (i := 0) (j := 2) (by decide)).mono_left
        (smul_startSet_subset_zero (k := 1) (by decide))
  | 1, 0 =>
      exact (startSet_disjoint (i := 0) (j := 1) (by decide)).mono_left
        (smul_startSet_subset_zero (k := 2) (by decide))
  | 1, 1 =>
      exact (startSet_disjoint (i := 0) (j := 2) (by decide)).mono_left
        (smul_startSet_subset_zero (k := 2) (by decide))

theorem pingX_condition : ∀ i, pingGen i • (pingY i)ᶜ ⊆ pingX i := by
  intro i
  match i with
  | 0 =>
      show (letterFlip 0 * letterFlip 1) • (startSet 1)ᶜ ⊆ letterFlip 0 • startSet 1
      rw [mul_smul]
      exact Set.smul_set_mono (letterFlip_smul_compl_subset 1)
  | 1 =>
      show (letterFlip 0 * letterFlip 2) • (startSet 2)ᶜ ⊆ letterFlip 0 • startSet 2
      rw [mul_smul]
      exact Set.smul_set_mono (letterFlip_smul_compl_subset 2)

theorem pingY_condition : ∀ i, pingGen⁻¹ i • (pingX i)ᶜ ⊆ pingY i := by
  have hcancel : ∀ S : Set RedWord,
      letterFlip 0 • (letterFlip 0 • S) = S := by
    intro S
    rw [← mul_smul, letterFlip_mul_self, one_smul]
  intro i
  match i with
  | 0 =>
      show ((letterFlip 0 * letterFlip 1)⁻¹) • (letterFlip 0 • startSet 1)ᶜ
        ⊆ startSet 1
      have key : ((letterFlip 0 * letterFlip 1)⁻¹) • (letterFlip 0 • startSet 1)ᶜ
          = letterFlip 1 • (startSet 1)ᶜ := by
        rw [mul_inv_rev, letterFlip_inv, letterFlip_inv, ← Set.smul_set_compl,
          mul_smul, hcancel]
      rw [key]
      exact letterFlip_smul_compl_subset 1
  | 1 =>
      show ((letterFlip 0 * letterFlip 2)⁻¹) • (letterFlip 0 • startSet 2)ᶜ
        ⊆ startSet 2
      have key : ((letterFlip 0 * letterFlip 2)⁻¹) • (letterFlip 0 • startSet 2)ᶜ
          = letterFlip 2 • (startSet 2)ᶜ := by
        rw [mul_inv_rev, letterFlip_inv, letterFlip_inv, ← Set.smul_set_compl,
          mul_smul, hcancel]
      rw [key]
      exact letterFlip_smul_compl_subset 2

/-- **Ping-pong.**  The two products of letter flips generate a free group of
rank two inside the permutations of the reduced words. -/
theorem pingGen_lift_injective : Function.Injective (FreeGroup.lift pingGen) :=
  FreeGroup.injective_lift_of_ping_pong pingGen pingX pingY
    pingX_nonempty pingX_disjoint pingY_disjoint pingXY_disjoint
    pingX_condition pingY_condition

/-! ## The free group of rank two is nonabelian

The free subgroup produced below is nonabelian.  That is a statement about
`FreeGroup (Fin 2)` alone, and it is settled by one nonabelian finite image:
the two transpositions `(0 1)` and `(1 2)` of `Fin 3` do not commute.
-/

/-- Two non-commuting transpositions of `Fin 3`. -/
def swapPair : Fin 2 → Equiv.Perm (Fin 3)
  | 0 => Equiv.swap 0 1
  | 1 => Equiv.swap 1 2

theorem freeGroupTwo_generators_not_commute :
    (FreeGroup.of (0 : Fin 2)) * (FreeGroup.of (1 : Fin 2))
      ≠ (FreeGroup.of (1 : Fin 2)) * (FreeGroup.of (0 : Fin 2)) := by
  intro h
  have h2 := congrArg (FreeGroup.lift swapPair) h
  simp only [map_mul, FreeGroup.lift_apply_of] at h2
  have h3 : (swapPair 0 * swapPair 1) 2 = (swapPair 1 * swapPair 0) 2 := by
    rw [h2]
  exact absurd h3 (by decide)

/-! ## Transport to the Clifford group of the orbital graph -/

noncomputable section

/-- The three-flip test assignment: three marked sites carry the three letter
flips, and every other site carries the identity. -/
def threeLamp (ξ η θ : Site) : Site → Equiv.Perm RedWord :=
  letI : DecidableEq Site := Classical.decEq Site
  fun σ =>
    if σ = ξ then letterFlip 0
    else if σ = η then letterFlip 1
    else if σ = θ then letterFlip 2 else 1

theorem threeLamp_first (ξ η θ : Site) :
    threeLamp ξ η θ ξ = letterFlip 0 := by
  letI : DecidableEq Site := Classical.decEq Site
  show (if ξ = ξ then letterFlip 0
    else if ξ = η then letterFlip 1
    else if ξ = θ then letterFlip 2 else 1) = _
  rw [if_pos rfl]

theorem threeLamp_second {ξ η θ : Site} (h : η ≠ ξ) :
    threeLamp ξ η θ η = letterFlip 1 := by
  letI : DecidableEq Site := Classical.decEq Site
  show (if η = ξ then letterFlip 0
    else if η = η then letterFlip 1
    else if η = θ then letterFlip 2 else 1) = _
  rw [if_neg h, if_pos rfl]

theorem threeLamp_third {ξ η θ : Site} (h1 : θ ≠ ξ) (h2 : θ ≠ η) :
    threeLamp ξ η θ θ = letterFlip 2 := by
  letI : DecidableEq Site := Classical.decEq Site
  show (if θ = ξ then letterFlip 0
    else if θ = η then letterFlip 1
    else if θ = θ then letterFlip 2 else 1) = _
  rw [if_neg h1, if_neg h2, if_pos rfl]

theorem threeLamp_other {ξ η θ σ : Site} (h1 : σ ≠ ξ) (h2 : σ ≠ η)
    (h3 : σ ≠ θ) : threeLamp ξ η θ σ = 1 := by
  letI : DecidableEq Site := Classical.decEq Site
  show (if σ = ξ then letterFlip 0
    else if σ = η then letterFlip 1
    else if σ = θ then letterFlip 2 else 1) = _
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem threeLamp_sq (ξ η θ σ : Site) : threeLamp ξ η θ σ ^ 2 = 1 := by
  letI : DecidableEq Site := Classical.decEq Site
  have hflip : ∀ i : Fin 3, letterFlip i ^ 2 = 1 := by
    intro i
    rw [pow_two]
    exact letterFlip_mul_self i
  show (if σ = ξ then letterFlip 0
    else if σ = η then letterFlip 1
    else if σ = θ then letterFlip 2 else 1) ^ 2 = 1
  by_cases h1 : σ = ξ
  · rw [if_pos h1]
    exact hflip 0
  · rw [if_neg h1]
    by_cases h2 : σ = η
    · rw [if_pos h2]
      exact hflip 1
    · rw [if_neg h2]
      by_cases h3 : σ = θ
      · rw [if_pos h3]
        exact hflip 2
      · rw [if_neg h3, one_pow]

/-- Every braiding relator of `C(𝒢)` survives the three-flip assignment: an
edge of `𝒢` never joins two of the three marked sites, and every unmarked site
carries the identity. -/
theorem threeLamp_braiding {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ) :
    ∀ a b : Site, Adjacent a b →
      ⁅threeLamp ξ η θ a, threeLamp ξ η θ b⁆ = 1 := by
  have hmarked : ∀ s : Site, threeLamp ξ η θ s ≠ 1 →
      s = ξ ∨ s = η ∨ s = θ := by
    intro s hs
    by_contra hcon
    push Not at hcon
    exact hs (threeLamp_other hcon.1 hcon.2.1 hcon.2.2)
  intro a b hab
  by_cases ha : threeLamp ξ η θ a = 1
  · rw [ha]
    exact commutatorElement_one_left _
  by_cases hb : threeLamp ξ η θ b = 1
  · rw [hb]
    exact commutatorElement_one_right _
  rcases eq_or_ne a b with rfl | hne
  · exact commutatorElement_self _
  rcases hmarked a ha with rfl | rfl | rfl
  · rcases hmarked b hb with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact absurd hab hξη
    · exact absurd hab hξθ
  · rcases hmarked b hb with rfl | rfl | rfl
    · exact absurd hab.flip hξη
    · exact absurd rfl hne
    · exact absurd hab hηθ
  · rcases hmarked b hb with rfl | rfl | rfl
    · exact absurd hab.flip hξθ
    · exact absurd hab.flip hηθ
    · exact absurd rfl hne

/-- **The test homomorphism.**  Three pairwise non-adjacent lamps go to the
three letter flips; the sign and every other lamp die. -/
def threeLampLift {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ) :
    LampFactor →* Equiv.Perm RedWord :=
  lampLift (1 : Equiv.Perm RedWord) (threeLamp ξ η θ) (one_pow 2)
    (threeLamp_sq ξ η θ) (fun _ => Commute.one_left _)
    (threeLamp_braiding hξη hξθ hηθ)

theorem threeLampLift_first {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ) :
    threeLampLift hξη hξθ hηθ (lampAt ξ) = letterFlip 0 := by
  rw [threeLampLift, lampLift_at, threeLamp_first]

theorem threeLampLift_second {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ) (h : η ≠ ξ) :
    threeLampLift hξη hξθ hηθ (lampAt η) = letterFlip 1 := by
  rw [threeLampLift, lampLift_at, threeLamp_second h]

theorem threeLampLift_third {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ) (h1 : θ ≠ ξ) (h2 : θ ≠ η) :
    threeLampLift hξη hξθ hηθ (lampAt θ) = letterFlip 2 := by
  rw [threeLampLift, lampLift_at, threeLamp_third h1 h2]

/-- The two elements of `C(𝒢)` that generate the free subgroup: the products of
the first marked lamp with each of the other two. -/
def lampFreePair (ξ η θ : Site) : Fin 2 → LampFactor
  | 0 => lampAt ξ * lampAt η
  | 1 => lampAt ξ * lampAt θ

theorem threeLampLift_comp_lift {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ)
    (hne1 : η ≠ ξ) (hne2 : θ ≠ ξ) (hne3 : θ ≠ η) :
    (threeLampLift hξη hξθ hηθ).comp (FreeGroup.lift (lampFreePair ξ η θ))
      = FreeGroup.lift pingGen := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  match i with
  | 0 =>
      show threeLampLift hξη hξθ hηθ (lampAt ξ * lampAt η)
        = letterFlip 0 * letterFlip 1
      rw [map_mul, threeLampLift_first, threeLampLift_second _ _ _ hne1]
  | 1 =>
      show threeLampLift hξη hξθ hηθ (lampAt ξ * lampAt θ)
        = letterFlip 0 * letterFlip 2
      rw [map_mul, threeLampLift_first, threeLampLift_third _ _ _ hne2 hne3]

/-- **Three non-adjacent lamps generate a free group of rank two.**  This is the
second half of the manuscript's sentence about `C(𝒢)`; the first half, the
infinite dihedral group from two lamps, is
`not_isLocallyFiniteGroup_lampFactor`. -/
theorem lampFreePair_lift_injective {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ)
    (hne1 : η ≠ ξ) (hne2 : θ ≠ ξ) (hne3 : θ ≠ η) :
    Function.Injective (FreeGroup.lift (lampFreePair ξ η θ)) := by
  have hcomp : Function.Injective
      (⇑(threeLampLift hξη hξθ hηθ) ∘
        ⇑(FreeGroup.lift (lampFreePair ξ η θ))) := by
    rw [← MonoidHom.coe_comp,
      threeLampLift_comp_lift hξη hξθ hηθ hne1 hne2 hne3]
    exact pingGen_lift_injective
  exact hcomp.of_comp

/-- The two generators of that free subgroup do not commute, so the subgroup is
*nonabelian* free and not merely free. -/
theorem lampFreePair_not_commute {ξ η θ : Site} (hξη : ¬ Adjacent ξ η)
    (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ)
    (hne1 : η ≠ ξ) (hne2 : θ ≠ ξ) (hne3 : θ ≠ η) :
    ¬ Commute (lampAt ξ * lampAt η) (lampAt ξ * lampAt θ) := by
  intro hcomm
  refine freeGroupTwo_generators_not_commute ?_
  refine lampFreePair_lift_injective hξη hξθ hηθ hne1 hne2 hne3 ?_
  simp only [map_mul, FreeGroup.lift_apply_of]
  exact hcomm.eq

/-- **The printed sentence, from non-adjacency.**  Three pairwise distinct,
pairwise non-adjacent sites give a subgroup of `C(𝒢)` isomorphic to the free
group of rank two. -/
theorem exists_free_subgroup_of_three_nonadjacent {ξ η θ : Site}
    (hξη : ¬ Adjacent ξ η) (hξθ : ¬ Adjacent ξ θ) (hηθ : ¬ Adjacent η θ)
    (hne1 : η ≠ ξ) (hne2 : θ ≠ ξ) (hne3 : θ ≠ η) :
    ∃ H : Subgroup LampFactor, Nonempty (FreeGroup (Fin 2) ≃* H) :=
  ⟨(FreeGroup.lift (lampFreePair ξ η θ)).range,
    ⟨MonoidHom.ofInjective
      (lampFreePair_lift_injective hξη hξθ hηθ hne1 hne2 hne3)⟩⟩

/-- **The printed sentence, from blocks.**  Three sites in three distinct blocks
give a nonabelian free subgroup of `C(𝒢)`: adjacent sites share a block by
`blockOf_eq_of_adjacent`, so distinct blocks give both distinctness and
non-adjacency for free. -/
theorem exists_free_subgroup_of_three_blocks {ξ η θ : Site}
    (h01 : blockOf ξ ≠ blockOf η) (h02 : blockOf ξ ≠ blockOf θ)
    (h12 : blockOf η ≠ blockOf θ) :
    ∃ H : Subgroup LampFactor, Nonempty (FreeGroup (Fin 2) ≃* H) :=
  exists_free_subgroup_of_three_nonadjacent
    (fun hadj => h01 (blockOf_eq_of_adjacent hadj))
    (fun hadj => h02 (blockOf_eq_of_adjacent hadj))
    (fun hadj => h12 (blockOf_eq_of_adjacent hadj))
    (fun h => h01 (by rw [h])) (fun h => h02 (by rw [h]))
    (fun h => h12 (by rw [h]))

/-- The same conclusion with nonabelianness recorded explicitly. -/
theorem exists_nonabelian_free_subgroup_of_three_blocks {ξ η θ : Site}
    (h01 : blockOf ξ ≠ blockOf η) (h02 : blockOf ξ ≠ blockOf θ)
    (h12 : blockOf η ≠ blockOf θ) :
    (∃ H : Subgroup LampFactor, Nonempty (FreeGroup (Fin 2) ≃* H)) ∧
      ¬ Commute (lampAt ξ * lampAt η) (lampAt ξ * lampAt θ) :=
  ⟨exists_free_subgroup_of_three_blocks h01 h02 h12,
    lampFreePair_not_commute
      (fun hadj => h01 (blockOf_eq_of_adjacent hadj))
      (fun hadj => h02 (blockOf_eq_of_adjacent hadj))
      (fun hadj => h12 (blockOf_eq_of_adjacent hadj))
      (fun h => h01 (by rw [h])) (fun h => h02 (by rw [h]))
      (fun h => h12 (by rw [h]))⟩

end

end CliffordLampGraph
end GroupApproximation
