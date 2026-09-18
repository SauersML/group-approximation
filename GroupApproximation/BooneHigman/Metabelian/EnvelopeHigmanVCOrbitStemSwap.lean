import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitStemRep
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# The empty-stem swaps (lane bh-met-92m)

Notation as in `EnvelopeHigmanVCOrbitStemRep`: `t = m(a, b)` with `a`, `b` incomparable and
`|b| = |a| + 1`, `U = higmanVCTreeNF_U d`, `S = higmanVCTreeNFWitPivot_S d`.

* `higmanVCOrbitStem_rep_mem_S`: `m(a, b yᴸ) · t ∈ S`.  For `L = m + 1`, the element
  `m(a, b yᴸ) t = (m(a, b yᴸ) t w) · w` lies in `H_R · U`, because `w = m(b, a y)` is
  balanced.  For `L = 0` it is `t² = 1`.
* `higmanVCOrbitStem_move_mem_S`: if `|s| = |r|` and `s ≠ r`, then `m(a, b r) t ∈ S` implies
  `m(a, b s) t ∈ S`.  Here `x = m(b s, b r) ∈ U` fixes the cone `a`, so
  `x m(a, b r) x⁻¹ = m(a, b s)`.  Also `t x t⁻¹ = m(a s, a r) ∈ U`, which gives the
  `N`-conjugation `higmanVCOrbitLong_conj_mem_S`.
* `higmanVCOrbitStem_swap_mem_S`: `m(a, b s) · t ∈ S` for every word `s`.
* `higmanVCOrbitStem_swap'_mem_S`: the twist `m(a s, b) · t ∈ S`, because
  `(m(a s, b) t)⁻¹ = m(b s, a) t = m(a, b s) t` and `S` is closed under inverses.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `x = 1 (x w) w` when `w² = 1`. -/
theorem higmanVCOrbitStem_rt_eq {G : Type*} [Group G] {x w : G} (hw : w * w = 1) :
    x = 1 * (x * w) * w := by
  rw [one_mul, mul_assoc, hw, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_rt_eq

/-- **Replicate swap.**  `m(a, b yᴸ) · t ∈ S`. -/
theorem higmanVCOrbitStem_rep_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) (y : Fin d) (L : ℕ) :
    higmanVCCommon_mk d (FreeGroup.of (a, b ++ List.replicate L y)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  cases L with
  | zero =>
    rw [List.replicate_zero, List.append_nil, higmanVCCommon_mk_sq]
    exact higmanVCTreeNFWitPivot_one_mem_S d
  | succ m =>
    have hW : higmanVCCommon_mk d (FreeGroup.of (b, a ++ [y])) ∈ higmanVCTreeNF_U d :=
      higmanVCTreeNF_letter_mem (by rw [List.length_append, List.length_singleton, hlen])
    exact higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, (higmanVCTreeNF_U d).one_mem,
      higmanVCOrbitStem_R a b (List.replicate m y), higmanVCOrbitStem_R_isAC hab hba _, _,
      higmanVCOrbitStem_rep_mem_H y m a b hab hba, _, hW,
      higmanVCOrbitStem_rt_eq (higmanVCCommon_mk_sq b (a ++ [y]))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_rep_mem_S

/-- Distinct tails of equal length are incomparable after a common stem. -/
theorem higmanVCOrbitStem_ne_prefix {d : ℕ} (c : List (Fin d)) {s r : List (Fin d)}
    (hsr : s ≠ r) (hl : s.length = r.length) : ¬ c ++ s <+: c ++ r := by
  rw [List.prefix_append_right_inj]
  exact fun h => hsr (h.eq_of_length hl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_ne_prefix

/-- **Moving the tail.**  For `|s| = |r|` and `s ≠ r`, `m(a, b r) t ∈ S → m(a, b s) t ∈ S`. -/
theorem higmanVCOrbitStem_move_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {s r : List (Fin d)} (hsr : s ≠ r) (hl : s.length = r.length)
    (hr : higmanVCCommon_mk d (FreeGroup.of (a, b ++ r)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d) :
    higmanVCCommon_mk d (FreeGroup.of (a, b ++ s)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have n1 : ¬ b ++ s <+: b ++ r := higmanVCOrbitStem_ne_prefix b hsr hl
  have n2 : ¬ b ++ r <+: b ++ s := higmanVCOrbitStem_ne_prefix b (Ne.symm hsr) hl.symm
  have m1 : ¬ a ++ s <+: a ++ r := higmanVCOrbitStem_ne_prefix a hsr hl
  have m2 : ¬ a ++ r <+: a ++ s := higmanVCOrbitStem_ne_prefix a (Ne.symm hsr) hl.symm
  have as1 : ¬ a <+: b ++ s :=
    higmanVCOrbitGen_incomp hab hba (List.prefix_refl a) (List.prefix_append b s)
  have as2 : ¬ b ++ s <+: a :=
    higmanVCOrbitGen_incomp hba hab (List.prefix_append b s) (List.prefix_refl a)
  have ar1 : ¬ a <+: b ++ r :=
    higmanVCOrbitGen_incomp hab hba (List.prefix_refl a) (List.prefix_append b r)
  have ar2 : ¬ b ++ r <+: a :=
    higmanVCOrbitGen_incomp hba hab (List.prefix_append b r) (List.prefix_refl a)
  have hx : higmanVCCommon_mk d (FreeGroup.of (b ++ s, b ++ r)) ∈ higmanVCTreeNF_U d :=
    higmanVCTreeNF_letter_mem (by rw [List.length_append, List.length_append, hl])
  have htx : higmanVCCommon_mk d (FreeGroup.of (a, b)) *
      higmanVCCommon_mk d (FreeGroup.of (b ++ s, b ++ r)) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ ∈ higmanVCTreeNF_U d := by
    rw [higmanVCOrbitGen_conj hab hba ((mapsCone_coneSwap_right hab hba).append s)
      ((mapsCone_coneSwap_right hab hba).append r) n1 n2 m1 m2]
    exact higmanVCTreeNF_letter_mem (by rw [List.length_append, List.length_append, hl])
  have hc : higmanVCCommon_mk d (FreeGroup.of (b ++ s, b ++ r)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b ++ r)) *
        (higmanVCCommon_mk d (FreeGroup.of (b ++ s, b ++ r)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (a, b ++ s)) :=
    higmanVCOrbitGen_conj n1 n2 (vgen_mapsCone_coneSwap_fix n1 n2 as1 as2 ar1 ar2)
      (mapsCone_coneSwap_right n1 n2) ar1 ar2 as1 as2
  rw [← hc]
  exact higmanVCOrbitLong_conj_mem_S hr hx htx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_move_mem_S

/-- **Empty-stem swap.**  `m(a, b s) · t ∈ S` for every word `s`. -/
theorem higmanVCOrbitStem_swap_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) (s : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (a, b ++ s)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  cases s with
  | nil =>
    rw [List.append_nil, higmanVCCommon_mk_sq]
    exact higmanVCTreeNFWitPivot_one_mem_S d
  | cons y s' =>
    have hrep := higmanVCOrbitStem_rep_mem_S hab hba hlen y (s'.length + 1)
    by_cases hs : y :: s' = List.replicate (s'.length + 1) y
    · rw [hs]
      exact hrep
    · exact higmanVCOrbitStem_move_mem_S hab hba hs
        (by rw [List.length_cons, List.length_replicate]) hrep

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_swap_mem_S

/-- The twist identity: `(σ t)⁻¹ = σ' t` when `σ² = t² = 1` and `t σ t⁻¹ = σ'`. -/
theorem higmanVCOrbitStem_twist_eq {G : Type*} [Group G] {σ t σ' : G} (hσ : σ * σ = 1)
    (ht : t * t = 1) (hc : t * σ * t⁻¹ = σ') : (σ * t)⁻¹ = σ' * t := by
  have h1 : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have h2 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  calc (σ * t)⁻¹ = t⁻¹ * σ⁻¹ := mul_inv_rev σ t
    _ = t * σ := by rw [h1, h2]
    _ = t * σ * t⁻¹ * t := by group
    _ = σ' * t := by rw [hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_twist_eq

/-- **Twisted empty-stem swap.**  `m(a s, b) · t ∈ S` for every word `s`. -/
theorem higmanVCOrbitStem_swap'_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) (s : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ s, b)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have hxy : ¬ a ++ s <+: b :=
    higmanVCOrbitGen_incomp hab hba (List.prefix_append a s) (List.prefix_refl b)
  have hyx : ¬ b <+: a ++ s :=
    higmanVCOrbitGen_incomp hba hab (List.prefix_refl b) (List.prefix_append a s)
  have hxy' : ¬ b ++ s <+: a :=
    higmanVCOrbitGen_incomp hba hab (List.prefix_append b s) (List.prefix_refl a)
  have hyx' : ¬ a <+: b ++ s :=
    higmanVCOrbitGen_incomp hab hba (List.prefix_refl a) (List.prefix_append b s)
  have hc : higmanVCCommon_mk d (FreeGroup.of (a, b)) *
      higmanVCCommon_mk d (FreeGroup.of (a ++ s, b)) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (b ++ s, a)) :=
    higmanVCOrbitGen_conj hab hba ((mapsCone_coneSwap_left hab hba).append s)
      (mapsCone_coneSwap_right hab hba) hxy hyx hxy' hyx'
  have e := higmanVCOrbitStem_twist_eq (higmanVCCommon_mk_sq (a ++ s) b)
    (higmanVCCommon_mk_sq a b) hc
  have hs := higmanVCOrbitStem_swap_mem_S hab hba hlen s
  rw [← higmanVCOrbitGen_symm hyx' hxy', ← e] at hs
  have hi := higmanVCOrbit_inv_mem_S hs
  rwa [inv_inv] at hi

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_swap'_mem_S

end GroupApproximation.BooneHigman.Metabelian.Envelope
