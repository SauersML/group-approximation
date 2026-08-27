import GroupApproximation.Monsters.SL2BraidPresentation

/-!
# Weyl relations in the rank-two braid presentation

Consequences of the two relators inside `SL2P = ⟨a, b ∣ aba = bab,
(aba)⁴⟩`, with `s = aba` the Weyl element and `t = ab` the rotation:

* the braid relation itself, and `s⁴ = 1`;
* the Weyl conjugations `s a s⁻¹ = b` and `s b s⁻¹ = a`;
* centrality of `s²`, hence normality of the subgroup it generates;
* the rotation identity `t³ = s²`;
* the Tietze cancellations `t⁻¹ s = a` and `s⁻¹ t² = b`, which show
  that `s` and `t` also generate.

These are the ingredients of the completeness argument for the rank-two
presentation: modulo the central subgroup `⟨s²⟩` the group is generated
by an involution `s` and a rotation `t` of order dividing three, and the
Tietze identities transport words back and forth.
-/

namespace GroupApproximation
namespace SL2WeylRelations

open SL2BraidPresentation PresentedGroupRelatorReplay

noncomputable section

/-- The first braid generator `a = e₁₂(1)`. -/
abbrev ga : SL2P := PresentedGroup.of 0

/-- The second braid generator `b = e₂₁(-1)`. -/
abbrev gb : SL2P := PresentedGroup.of 1

/-- The Weyl element `s = aba`. -/
def s : SL2P := ga * gb * ga

/-- The rotation `t = ab`. -/
def t : SL2P := ga * gb

/-- The word homomorphism onto the presented group. -/
abbrev sl2PWord : FreeGroup SL2BraidGenerator →* SL2P :=
  PresentedGroup.mk (sl2Relators : Set (FreeGroup SL2BraidGenerator))

private theorem relator_eq_one (i : Fin 2) :
    sl2PWord (sl2Relator i) = 1 :=
  PresentedGroup.one_of_mem (by simp [sl2Relators])

private theorem braid_aux :
    ga * gb * ga * gb⁻¹ * ga⁻¹ * gb⁻¹ = 1 := by
  show sl2PWord (sl2Relator 0) = 1
  exact relator_eq_one 0

/-- The braid relation `aba = bab` in the presented group. -/
theorem braid_rel : ga * gb * ga = gb * ga * gb := by
  calc ga * gb * ga
      = (ga * gb * ga * gb⁻¹ * ga⁻¹ * gb⁻¹) * (gb * ga * gb) := by group
    _ = 1 * (gb * ga * gb) := by rw [braid_aux]
    _ = gb * ga * gb := one_mul _

private theorem s_pow_four_aux :
    ga * gb * ga * ga * gb * ga * ga * gb * ga * ga * gb * ga = 1 := by
  show sl2PWord (sl2Relator 1) = 1
  exact relator_eq_one 1

/-- The Weyl element has order dividing four. -/
theorem s_pow_four : s * s * s * s = 1 := by
  calc s * s * s * s
      = ga * gb * ga * ga * gb * ga * ga * gb * ga * ga * gb * ga := by
        unfold s
        group
    _ = 1 := s_pow_four_aux

/-- The Weyl element in its second braid spelling. -/
theorem s_eq_bab : s = gb * ga * gb := braid_rel

/-- Weyl conjugation of the first generator. -/
theorem s_conj_a : s * ga * s⁻¹ = gb := by
  show ga * gb * ga * ga * (ga * gb * ga)⁻¹ = gb
  calc ga * gb * ga * ga * (ga * gb * ga)⁻¹
      = (ga * gb * ga) * gb⁻¹ * ga⁻¹ := by group
    _ = (gb * ga * gb) * gb⁻¹ * ga⁻¹ := by rw [braid_rel]
    _ = gb := by group

/-- Weyl conjugation of the second generator. -/
theorem s_conj_b : s * gb * s⁻¹ = ga := by
  rw [s_eq_bab]
  calc gb * ga * gb * gb * (gb * ga * gb)⁻¹
      = (gb * ga * gb) * ga⁻¹ * gb⁻¹ := by group
    _ = (ga * gb * ga) * ga⁻¹ * gb⁻¹ := by rw [← braid_rel]
    _ = ga := by group

private theorem s_sq_conj_a : s * s * ga * (s * s)⁻¹ = ga := by
  calc s * s * ga * (s * s)⁻¹
      = s * (s * ga * s⁻¹) * s⁻¹ := by group
    _ = s * gb * s⁻¹ := by rw [s_conj_a]
    _ = ga := s_conj_b

private theorem s_sq_conj_b : s * s * gb * (s * s)⁻¹ = gb := by
  calc s * s * gb * (s * s)⁻¹
      = s * (s * gb * s⁻¹) * s⁻¹ := by group
    _ = s * ga * s⁻¹ := by rw [s_conj_b]
    _ = gb := s_conj_a

/-- The square of the Weyl element is central. -/
theorem s_sq_commute (g : SL2P) : Commute (s * s) g := by
  have hmem : g ∈ (⊤ : Subgroup SL2P) := trivial
  rw [← PresentedGroup.closure_range_of] at hmem
  induction hmem using Subgroup.closure_induction with
  | mem h hgen =>
      obtain ⟨i, rfl⟩ := hgen
      match i with
      | 0 =>
          have hcalc : s * s * ga = ga * (s * s) := by
            calc s * s * ga
                = (s * s * ga * (s * s)⁻¹) * (s * s) := by group
              _ = ga * (s * s) := by rw [s_sq_conj_a]
          exact hcalc
      | 1 =>
          have hcalc : s * s * gb = gb * (s * s) := by
            calc s * s * gb
                = (s * s * gb * (s * s)⁻¹) * (s * s) := by group
              _ = gb * (s * s) := by rw [s_sq_conj_b]
          exact hcalc
  | one => exact Commute.one_right _
  | mul g₁ g₂ _ _ ih1 ih2 => exact ih1.mul_right ih2
  | inv g _ ih => exact ih.inv_right

/-- The rotation cubes to the central element. -/
theorem t_cubed : t * t * t = s * s := by
  have h : s * s = t * t * t := by
    show ga * gb * ga * (ga * gb * ga) = ga * gb * (ga * gb) * (ga * gb)
    calc ga * gb * ga * (ga * gb * ga)
        = ga * gb * (ga * (ga * gb * ga)) := by group
      _ = ga * gb * (ga * (gb * ga * gb)) := by rw [braid_rel]
      _ = ga * gb * (ga * gb) * (ga * gb) := by group
  exact h.symm

/-- Tietze cancellation: `t⁻¹ s = a`. -/
theorem t_inv_mul_s : t⁻¹ * s = ga := by
  show (ga * gb)⁻¹ * (ga * gb * ga) = ga
  group

/-- Tietze cancellation: `s⁻¹ t² = b`. -/
theorem s_inv_mul_t_sq : s⁻¹ * (t * t) = gb := by
  show (ga * gb * ga)⁻¹ * (ga * gb * (ga * gb)) = gb
  group

end

end SL2WeylRelations
end GroupApproximation
