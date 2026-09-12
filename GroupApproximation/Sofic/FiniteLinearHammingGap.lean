import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# The one-half Hamming gap for additive maps

Two distinct additive maps on a finite additive group disagree on at least
half of the source.  Translation by one disagreement point injects the
agreement set into the disagreement set.  Applied to linear automorphisms of
an elementary abelian lamp group, this is the discrete step in finite regular
normalizer rounding: a relator with Hamming defect below `1/2` is exact.
-/

namespace GroupApproximation

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Fintype V] [DecidableEq W]

/-- The finite set on which two additive maps agree. -/
def additiveAgreement (f g : V →+ W) : Finset V :=
  Finset.univ.filter fun x ↦ f x = g x

/-- The finite set on which two additive maps disagree. -/
def additiveDisagreement (f g : V →+ W) : Finset V :=
  Finset.univ.filter fun x ↦ f x ≠ g x

/-- Translation by any disagreement point injects the agreement set into the
disagreement set. -/
theorem card_additiveAgreement_le_card_additiveDisagreement
    (f g : V →+ W) (hfg : f ≠ g) :
    (additiveAgreement f g).card ≤ (additiveDisagreement f g).card := by
  classical
  have hpoint : ∃ v : V, f v ≠ g v := by
    by_contra h
    push Not at h
    exact hfg (AddMonoidHom.ext h)
  obtain ⟨v, hv⟩ := hpoint
  refine Finset.card_le_card_of_injOn (fun x ↦ x + v) ?_ ?_
  · intro x hx
    have hx' : f x = g x := by
      simpa [additiveAgreement] using hx
    have hne : f (x + v) ≠ g (x + v) := by
      intro hsum
      rw [map_add, map_add, hx'] at hsum
      exact hv (add_left_cancel hsum)
    simpa [additiveDisagreement] using hne
  · intro x _ y _ hxy
    exact add_right_cancel hxy

/-- **One-half gap.**  Distinct additive maps on a finite additive group
disagree at at least half of all source points. -/
theorem card_le_two_mul_card_additiveDisagreement
    (f g : V →+ W) (hfg : f ≠ g) :
    Fintype.card V ≤ 2 * (additiveDisagreement f g).card := by
  classical
  have hle := card_additiveAgreement_le_card_additiveDisagreement f g hfg
  have hsplit :
      (additiveAgreement f g).card + (additiveDisagreement f g).card =
        Fintype.card V := by
    simpa [additiveAgreement, additiveDisagreement] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (fun x ↦ f x = g x))
  omega

/-- Contrapositive form used to quantize approximate relators: disagreement
strictly below one half forces equality. -/
theorem additiveMap_eq_of_two_mul_card_disagreement_lt
    (f g : V →+ W)
    (hsmall : 2 * (additiveDisagreement f g).card < Fintype.card V) :
    f = g := by
  by_contra hfg
  exact (Nat.not_lt_of_ge
    (card_le_two_mul_card_additiveDisagreement f g hfg)) hsmall

end GroupApproximation
