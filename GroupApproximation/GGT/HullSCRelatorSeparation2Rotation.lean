import GroupApproximation.GGT.HullSCRelatorSeparation2ListFacts

/-!
# Step (b) over two subgroups: a matched block fixes the rotation

The argument of `GGT/HullSCRelatorSeparationRotation.lean`, over the alternating
relator.  A block letter occurs at exactly one position -- it is not a letter of
the base part, and the run has no repeated letter -- so two rotations carrying
the same block letter at the same offset are rotations by the same amount, hence
the same word.

Over one subgroup the run's repetition-freeness came from `List.Nodup.map` of an
injective map; here it is `HullSC.nodup_blockWord`, which needs only that the
exponents are distinct.  Everything else is the same argument.

This closes the case of Olshanskii's step (c) in which both members of the
symmetrized closure are rotations of the relator itself: it makes them the same
word, which the corrected separation excludes by `w' ≠ w`.  The surviving case
is a rotation of the relator against a rotation of its formal inverse.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Rotation

variable {G : Type u} [Group G]

/-- **A block letter of the alternating relator occurs at exactly one
position.**  It is not a letter of the base part
(`HullSC.notMem_map_base_of_comp`) and the run has no repeated letter
(`HullSC.nodup_blockWord`). -/
theorem blockPosition_unique₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnodup : ms.Nodup) {q q' : ℕ} {b : Bool} {x : G}
    (hq : (relatorWord₂ p h₀ h₁ ms)[q]? = some (GGT.RelLetter.comp b x))
    (hq' : (relatorWord₂ p h₀ h₁ ms)[q']? = some (GGT.RelLetter.comp b x)) :
    q = q' := by
  have hv : relatorWord₂ p h₀ h₁ ms
      = p.map GGT.RelLetter.base ++ blockWord h₀ h₁ false ms := rfl
  rw [hv] at hq hq'
  exact getElem?_append_index_eq (nodup_blockWord hinj false ms hnodup)
    (notMem_map_base_of_comp p b x) hq hq'

/-- **Two rotations of the alternating relator carrying the same block letter at
the same offset are equal.**

This is the step from "the blocks correspond" to "the two words are the same":
the block letter names its own position, so the two rotation indices are
congruent modulo the length, so the two rotations are the same list. -/
theorem rotate_eq_of_block_at_offset₂ {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnodup : ms.Nodup) {c c' d : ℕ} {b : Bool} {x : G}
    (hd : d < (relatorWord₂ p h₀ h₁ ms).length)
    (he : ((relatorWord₂ p h₀ h₁ ms).rotate c)[d]?
      = some (GGT.RelLetter.comp b x))
    (he' : ((relatorWord₂ p h₀ h₁ ms).rotate c')[d]?
      = some (GGT.RelLetter.comp b x)) :
    (relatorWord₂ p h₀ h₁ ms).rotate c
      = (relatorWord₂ p h₀ h₁ ms).rotate c' := by
  have hl : 0 < (relatorWord₂ p h₀ h₁ ms).length :=
    Nat.lt_of_le_of_lt (Nat.zero_le d) hd
  rw [getElem?_rotate_at hd, getElem?_rotate_head hl] at he
  rw [getElem?_rotate_at hd, getElem?_rotate_head hl] at he'
  have hmod : (c + d) % (relatorWord₂ p h₀ h₁ ms).length
      = (c' + d) % (relatorWord₂ p h₀ h₁ ms).length :=
    blockPosition_unique₂ hinj hnodup he he'
  refine rotate_cancel_right (d := d) ?_
  rw [← List.rotate_mod (relatorWord₂ p h₀ h₁ ms) (c + d),
    ← List.rotate_mod (relatorWord₂ p h₀ h₁ ms) (c' + d), hmod]

end Rotation

/-! ## The hypothesis, for the core -/

section Core

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The injectivity hypothesis, for the two loxodromic elements of the
core.**  Both have infinite order, so both power maps are injective; the `if`
selects between them by index. -/
theorem injective_pow_ite_lox (E : HypEmbeddedCore₂ A N) (b : Bool) :
    Function.Injective
      (fun n : ℕ => (if b then E.lox true else E.lox false) ^ n) := by
  rw [ite_lox_eq E b]
  exact injective_pow_lox₂ E b

end Core

end HullSC
end GroupApproximation
