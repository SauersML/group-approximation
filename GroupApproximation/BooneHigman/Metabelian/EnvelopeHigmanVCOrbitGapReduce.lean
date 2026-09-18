import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGapTwist
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonPush
import GroupApproximation.Meta.AxiomGuard

/-!
# `t`-balanced near letters, and residual `W''` (lane bh-met-91d)

Notation as in `EnvelopeHigmanVCOrbitGapMix`, with `|b| = |a| + 1`.

**Right peel of `t`-balanced letters (proved).**  A near letter `(a e, b e')` with
`|e'| = |e| + 1` changes length by `|e'| - |e| + 1 = 2`, so it is not in `U`.  But the
conjugation relation for the pivot gives `(a e, b e') = t (b e, a e') t⁻¹`
(`higmanVCOrbitGap_letter_eq_conj`), and `(b e, a e')` is balanced.  So any `g ∈ U` times
such a letter is mixed, and it passes the pivot: `g (a e, b e') t ∈ S`
(`higmanVCOrbitGap_U_letter_mem_S`).  This covers the 91d example
`swap(001, 011) · swap(000, 01000)` (`e = 0`, `e' = 00`), which `W'` leaves open.

**Residual `W''` = `HigmanVCOrbitGapStatement`.**  This is the pivot closure for non-mixed
`h` only.  `higmanVCOrbitGap_orbit_of_gap : W'' → W'`.  See the module docstring of
`EnvelopeHigmanVCOrbitGapMix` for the LOUD strength statement: `W''` is Prop-equivalent to
`W'` and is strictly smaller in proof content.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Appending suffixes keeps incomparable words incomparable. -/
theorem higmanVCOrbitGap_incomp_append {d : ℕ} {x y : List (Fin d)} (h1 : ¬ x <+: y)
    (h2 : ¬ y <+: x) (e e' : List (Fin d)) : ¬ x ++ e <+: y ++ e' := by
  intro h
  rcases List.prefix_or_prefix_of_prefix ((List.prefix_append x e).trans h)
      (List.prefix_append y e') with h' | h'
  · exact h1 h'
  · exact h2 h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_incomp_append

/-- **Conjugation by the pivot.**  `(a e, b e') = t (b e, a e') t⁻¹` in `Q`. -/
theorem higmanVCOrbitGap_letter_eq_conj {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (e e' : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ e, b ++ e')) =
      higmanVCCommon_mk d (FreeGroup.of (a, b)) *
        higmanVCCommon_mk d (FreeGroup.of (b ++ e, a ++ e')) *
          (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ := by
  have hr := higmanVCCommon_mk_rel (higmanVCCommon_conj_mem hab hba
    ((mapsCone_coneSwap_right hab hba).append e) ((mapsCone_coneSwap_left hab hba).append e')
    (higmanVCOrbitGap_incomp_append hba hab e e') (higmanVCOrbitGap_incomp_append hab hba e' e)
    (higmanVCOrbitGap_incomp_append hab hba e e') (higmanVCOrbitGap_incomp_append hba hab e' e))
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hr
  exact (mul_inv_eq_one.mp hr).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_letter_eq_conj

/-- A `t`-balanced near letter on the right preserves the mixed class. -/
theorem higmanVCOrbitGap_mix_mul_letter {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {h : higmanVCCommon_Q d}
    (hh : higmanVCOrbitGap_Mix d a b h) {e e' : List (Fin d)}
    (he : e'.length = e.length + 1) :
    higmanVCOrbitGap_Mix d a b (h * higmanVCCommon_mk d (FreeGroup.of (a ++ e, b ++ e'))) := by
  rw [higmanVCOrbitGap_letter_eq_conj hab hba e e']
  refine higmanVCOrbitGap_mix_mul_conj hh (higmanVCTreeNF_letter_mem ?_)
  simp only [List.length_append]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_mix_mul_letter

/-- **Concrete discharge.**  For `g ∈ U` and `|e'| = |e| + 1`, `g (a e, b e') t ∈ S`. -/
theorem higmanVCOrbitGap_U_letter_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) {g : higmanVCCommon_Q d}
    (hg : g ∈ higmanVCTreeNF_U d) {e e' : List (Fin d)} (he : e'.length = e.length + 1) :
    g * higmanVCCommon_mk d (FreeGroup.of (a ++ e, b ++ e')) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d :=
  higmanVCOrbitGap_mix_mem_S hab hba
    (higmanVCOrbitGap_mix_mul_letter hab hba hlen (higmanVCOrbitGap_mix_of_U hab hba hg) he)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_U_letter_mem_S

/-- The pivot closure, required only for non-mixed `h`. -/
def higmanVCOrbitGap_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ¬ higmanVCOrbitGap_Mix d a b h →
        h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_Closed

/-- **Residual W''**: the pivot closure for non-mixed `h`.  LOUD: `W'' ⇔ W' ⇔ W ⇔ Z` as
Props.  `W''` is strictly smaller than `W'` in proof content only: every mixed `h`, a class
strictly larger than symmetric ∪ balanced ∪ twisted-balanced, is discharged. -/
def HigmanVCOrbitGapStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCOrbitGap_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCOrbitGapStatement

/-- **`W'' → W'`.** -/
theorem higmanVCOrbitGap_orbit_of_gap (hG : HigmanVCOrbitGapStatement) :
    HigmanVCOrbitStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hG d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL hM h hh _ _ _
  by_cases hX : higmanVCOrbitGap_Mix d a b h
  · exact higmanVCOrbitGap_mix_mem_S hab hba hX
  · exact hcl C hC hL hM h hh hX

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_orbit_of_gap

/-- **`W'' → W`.** -/
theorem higmanVCOrbitGap_W_of_gap (hG : HigmanVCOrbitGapStatement) :
    HigmanVCLeafExpStatement :=
  higmanVCOrbit_W_of_orbit (higmanVCOrbitGap_orbit_of_gap hG)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_W_of_gap

/-- **Root wiring.**  `W''` and the short-relation section `τ` give the swap section. -/
theorem higmanVCOrbitGap_swapSection_of_tau (hG : HigmanVCOrbitGapStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVSwapSectionStatement :=
  higmanVCOrbit_swapSection_of_orbit_of_tau (higmanVCOrbitGap_orbit_of_gap hG) hB

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGap_swapSection_of_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
