import GroupApproximation.Matching.FinitePartialBijection

/-!
# Transporting partial arrows through co-large partial bridges

The compressor functor sends an arrow between source components across the
overlap arrows from those components to their matched targets.  At finite
level those overlap arrows are partial, so ordinary conjugation is replaced
by the sandwich

`u.symm.trans f |>.trans v`.

This file proves the two quantitative facts needed to descend that operation
to cluster quotients: it is Lipschitz up to the missing mass of the two
bridges, and it respects composition up to the missing mass of the bridges
and the two arrows.  Every error below is an explicit finite cardinality.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {X X' Y Y' Z Z' : FiniteModel}

/-- Transport a partial arrow through partial bridges at its source and
target.  Composition is written from left to right. -/
noncomputable def sandwich
    (u : FinitePartialBijection X X')
    (v : FinitePartialBijection Y Y')
    (f : FinitePartialBijection X Y) :
    FinitePartialBijection X' Y' :=
  (u.symm.trans f).trans v

/-- Reversing a transported arrow reverses the original arrow and exchanges
the two bridges. -/
theorem sandwich_symm
    (u : FinitePartialBijection X X')
    (v : FinitePartialBijection Y Y')
    (f : FinitePartialBijection X Y) :
    (sandwich u v f).symm = sandwich v u f.symm := by
  simp only [sandwich, symm_trans, symm_symm, trans_assoc]

/-- Transporting two arrows through the same partial bridges increases their
two-sided disagreement by at most the missing mass of those bridges. -/
theorem twoSidedDisagreement_sandwich_le
    (u : FinitePartialBijection X X')
    (v : FinitePartialBijection Y Y')
    (f g : FinitePartialBijection X Y) :
    (sandwich u v f).twoSidedDisagreement (sandwich u v g) ≤
      u.sourceDefect + u.targetDefect +
        f.twoSidedDisagreement g +
          (v.sourceDefect + v.targetDefect) := by
  have hleft := twoSidedDisagreement_trans_le u.symm u.symm f g
  have houter := twoSidedDisagreement_trans_le
    (u.symm.trans f) (u.symm.trans g) v v
  simp only [sandwich, twoSidedDisagreement_self,
    sourceDefect_symm, targetDefect_symm] at hleft houter ⊢
  omega

/-- The sandwich of the identity is precisely the partial identity on the
range of the bridge. -/
theorem sandwich_refl
    (u : FinitePartialBijection X X') :
    sandwich u u (refl X) = reflOn u.target := by
  simp only [sandwich, trans_refl, symm_trans_self]

/-- Exact identity-error formula for a partial bridge. -/
theorem twoSidedDisagreement_sandwich_refl
    (u : FinitePartialBijection X X') :
    (sandwich u u (refl X)).twoSidedDisagreement (refl X') =
      2 * u.targetDefect := by
  rw [sandwich_refl, twoSidedDisagreement_reflOn_refl]
  rfl

/-- Inserting the partial identity `v.trans v.symm` between two arrows costs
at most twice the source defect of `v`, together with the self-defects forced
by composing partial maps in the two-sided disagreement metric.  This is the
finite quantitative core of compatibility of `sandwich` with composition. -/
theorem twoSidedDisagreement_sandwich_trans_le
    (u : FinitePartialBijection X X')
    (v : FinitePartialBijection Y Y')
    (w : FinitePartialBijection Z Z')
    (f : FinitePartialBijection X Y)
    (g : FinitePartialBijection Y Z) :
    (sandwich u w (f.trans g)).twoSidedDisagreement
        ((sandwich u v f).trans (sandwich v w g)) ≤
      (u.sourceDefect + u.targetDefect) +
        (f.sourceDefect + f.targetDefect) +
          2 * v.sourceDefect +
            (g.sourceDefect + g.targetDefect) +
              (w.sourceDefect + w.targetDefect) := by
  let p : FinitePartialBijection X' Y := u.symm.trans f
  let mid : FinitePartialBijection Y Y := v.trans v.symm
  have hmid : mid.twoSidedDisagreement (refl Y) = 2 * v.sourceDefect := by
    dsimp only [mid]
    rw [trans_symm, twoSidedDisagreement_reflOn_refl]
    rfl
  have hpSelf : p.twoSidedDisagreement p ≤
      u.symm.twoSidedDisagreement u.symm +
        f.twoSidedDisagreement f := by
    exact twoSidedDisagreement_trans_le u.symm u.symm f f
  have hinsert := twoSidedDisagreement_trans_le p p mid (refl Y)
  have hg := twoSidedDisagreement_trans_le
    (p.trans mid) (p.trans (refl Y)) g g
  have hw := twoSidedDisagreement_trans_le
    ((p.trans mid).trans g) ((p.trans (refl Y)).trans g) w w
  simp only [twoSidedDisagreement_self, sourceDefect_symm,
    targetDefect_symm] at hpSelf hinsert hg hw
  rw [hmid] at hinsert
  have hshapeLeft :
      sandwich u w (f.trans g) = ((p.trans (refl Y)).trans g).trans w := by
    simp only [sandwich, p, trans_refl, trans_assoc]
  have hshapeRight :
      (sandwich u v f).trans (sandwich v w g) =
        ((p.trans mid).trans g).trans w := by
    simp only [sandwich, p, mid, trans_assoc]
  rw [hshapeLeft, hshapeRight]
  rw [twoSidedDisagreement_comm]
  omega

/-- Transporting an arrow across two partial bridges and then back changes it
only by the missing source mass of those bridges, together with the arrow's
own self-defect. -/
theorem twoSidedDisagreement_sandwich_roundtrip_le
    (u : FinitePartialBijection X X')
    (v : FinitePartialBijection Y Y')
    (f : FinitePartialBijection X Y) :
    (sandwich u.symm v.symm (sandwich u v f)).twoSidedDisagreement f ≤
      2 * u.sourceDefect + (f.sourceDefect + f.targetDefect) +
        2 * v.sourceDefect := by
  let leftId : FinitePartialBijection X X := u.trans u.symm
  let rightId : FinitePartialBijection Y Y := v.trans v.symm
  have hleftId : leftId.twoSidedDisagreement (refl X) =
      2 * u.sourceDefect := by
    dsimp only [leftId]
    rw [trans_symm, twoSidedDisagreement_reflOn_refl]
    rfl
  have hrightId : rightId.twoSidedDisagreement (refl Y) =
      2 * v.sourceDefect := by
    dsimp only [rightId]
    rw [trans_symm, twoSidedDisagreement_reflOn_refl]
    rfl
  have hleft := twoSidedDisagreement_trans_le leftId (refl X) f f
  have hright := twoSidedDisagreement_trans_le
    (leftId.trans f) ((refl X).trans f) rightId (refl Y)
  simp only [twoSidedDisagreement_self, refl_trans, trans_refl] at hleft hright
  rw [hleftId] at hleft
  rw [hrightId] at hright
  have hshape : sandwich u.symm v.symm (sandwich u v f) =
      (leftId.trans f).trans rightId := by
    simp only [sandwich, leftId, rightId, symm_symm, trans_assoc]
  rw [hshape]
  omega

end FinitePartialBijection
end GroupApproximation
