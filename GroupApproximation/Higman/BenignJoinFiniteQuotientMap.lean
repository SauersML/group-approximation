import GroupApproximation.Higman.CentralHNNFiniteQuotientMap
import GroupApproximation.Higman.BenignJoin

/-!
# Finite-quotient maps for the two-stage benign join

A pair of homomorphisms out of the two witness ambients induces maps through
both central HNN stages used by Higman's join.  The target edge at each stage
is the literal image of the source edge.  These are the maps through which a
finite normal-form obstruction is reflected before applying finite-base
subgroup separability.
-/

namespace GroupApproximation
namespace Higman
namespace BenignJoinFiniteQuotientMap

noncomputable section

variable {G : Type} [Group G] {A₁ A₂ : Subgroup G}
variable (w₁ : BenignWitness A₁) (w₂ : BenignWitness A₂)
variable {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂]

/-- The product map on the base of the join tower. -/
def baseMap (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :
    JoinBase w₁ w₂ →* Q₁ × Q₂ :=
  q₁.prodMap q₂

/-- The finite-quotient target of the first central HNN stage. -/
abbrev TargetLevel1 (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :=
  CentHNN ((joinM₁ w₁ w₂).map (baseMap w₁ w₂ q₁ q₂))

/-- The map through the first central HNN stage. -/
def level1Map (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :
    JoinLevel1 w₁ w₂ →* TargetLevel1 w₁ w₂ q₁ q₂ :=
  CentralHNNFiniteQuotientMap.map (joinM₁ w₁ w₂)
    (baseMap w₁ w₂ q₁ q₂)

@[simp] theorem level1Map_of
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂)
    (g : JoinBase w₁ w₂) :
    level1Map w₁ w₂ q₁ q₂ (HNNExtension.of g) =
      HNNExtension.of (baseMap w₁ w₂ q₁ q₂ g) := by
  exact CentralHNNFiniteQuotientMap.map_of _ _ _

@[simp] theorem level1Map_t
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :
    level1Map w₁ w₂ q₁ q₂
        (HNNExtension.t : JoinLevel1 w₁ w₂) =
      HNNExtension.t := by
  exact CentralHNNFiniteQuotientMap.map_t _ _

/-- First-stage block words are mapped coefficientwise. -/
@[simp] theorem level1Map_blockOf
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂)
    (p : JoinBase w₁ w₂ × JoinBase w₁ w₂) :
    level1Map w₁ w₂ q₁ q₂
        (Pinch.blockOf (joinM₁ w₁ w₂) p) =
      Pinch.blockOf
        ((joinM₁ w₁ w₂).map (baseMap w₁ w₂ q₁ q₂))
        (baseMap w₁ w₂ q₁ q₂ p.1,
          baseMap w₁ w₂ q₁ q₂ p.2) := by
  simp [Pinch.blockOf]

/-- First-stage block spellings are mapped coefficientwise. -/
theorem level1Map_word
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂)
    (z : JoinBase w₁ w₂)
    (l : List (JoinBase w₁ w₂ × JoinBase w₁ w₂)) :
    level1Map w₁ w₂ q₁ q₂
        (Pinch.word (joinM₁ w₁ w₂) z l) =
      Pinch.word
        ((joinM₁ w₁ w₂).map (baseMap w₁ w₂ q₁ q₂))
        (baseMap w₁ w₂ q₁ q₂ z)
        (l.map fun p ↦
          (baseMap w₁ w₂ q₁ q₂ p.1,
            baseMap w₁ w₂ q₁ q₂ p.2)) := by
  simp [Pinch.word, map_list_prod, List.map_map, Function.comp_def]

/-- The image of the second edge in the first finite-quotient stage. -/
abbrev TargetM₂ (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :
    Subgroup (TargetLevel1 w₁ w₂ q₁ q₂) :=
  (joinM₂' w₁ w₂).map (level1Map w₁ w₂ q₁ q₂)

/-- The finite-quotient target of the full two-stage join tower. -/
abbrev TargetLevel2 (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :=
  CentHNN (TargetM₂ w₁ w₂ q₁ q₂)

/-- The induced map through both central HNN stages. -/
def level2Map (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :
    JoinLevel2 w₁ w₂ →* TargetLevel2 w₁ w₂ q₁ q₂ :=
  CentralHNNFiniteQuotientMap.map (joinM₂' w₁ w₂)
    (level1Map w₁ w₂ q₁ q₂)

@[simp] theorem level2Map_of
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂)
    (g : JoinLevel1 w₁ w₂) :
    level2Map w₁ w₂ q₁ q₂ (HNNExtension.of g) =
      HNNExtension.of (level1Map w₁ w₂ q₁ q₂ g) := by
  exact CentralHNNFiniteQuotientMap.map_of _ _ _

@[simp] theorem level2Map_t
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂) :
    level2Map w₁ w₂ q₁ q₂
        (HNNExtension.t : JoinLevel2 w₁ w₂) =
      HNNExtension.t := by
  exact CentralHNNFiniteQuotientMap.map_t _ _

/-- Second-stage block words are mapped coefficientwise. -/
@[simp] theorem level2Map_blockOf
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂)
    (p : JoinLevel1 w₁ w₂ × JoinLevel1 w₁ w₂) :
    level2Map w₁ w₂ q₁ q₂
        (Pinch.blockOf (joinM₂' w₁ w₂) p) =
      Pinch.blockOf (TargetM₂ w₁ w₂ q₁ q₂)
        (level1Map w₁ w₂ q₁ q₂ p.1,
          level1Map w₁ w₂ q₁ q₂ p.2) := by
  simp [Pinch.blockOf]

/-- Second-stage block spellings are mapped coefficientwise. -/
theorem level2Map_word
    (q₁ : w₁.K →* Q₁) (q₂ : w₂.K →* Q₂)
    (z : JoinLevel1 w₁ w₂)
    (l : List (JoinLevel1 w₁ w₂ × JoinLevel1 w₁ w₂)) :
    level2Map w₁ w₂ q₁ q₂
        (Pinch.word (joinM₂' w₁ w₂) z l) =
      Pinch.word (TargetM₂ w₁ w₂ q₁ q₂)
        (level1Map w₁ w₂ q₁ q₂ z)
        (l.map fun p ↦
          (level1Map w₁ w₂ q₁ q₂ p.1,
            level1Map w₁ w₂ q₁ q₂ p.2)) := by
  simp [Pinch.word, map_list_prod, List.map_map, Function.comp_def]

end

end BenignJoinFiniteQuotientMap
end Higman
end GroupApproximation
