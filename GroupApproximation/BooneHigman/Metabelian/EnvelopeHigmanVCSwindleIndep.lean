import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindlePhi
import GroupApproximation.Meta.AxiomGuard

/-!
# Prefix independence of `φ_c` on the kernel (lane bh-hig-02)

For incomparable words `c`, `c'` the generator `s = (c, c')` conjugates `φ_c` into `φ_{c'}`
(`higSw_conj_phi`).  Since `Z = ker Ē` is central in `Q` for `1 < d` (`higSw_central`), for
`z ∈ Z` the value `φ_c z` does not depend on the nonempty prefix `c` (`higSw_phi_ker_indep`).
Consequently `w = φ_c z` is fixed by every `φ_{c'}` with `c'` nonempty (`higSw_phi_ker_fixed`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Centrality of `Z = ker Ē`** in `Q`, for `1 < d`. -/
theorem higSw_central {d : ℕ} (hd : 1 < d) {z : higmanVCCommon_Q d}
    (hz : z ∈ (higmanVCTreeNF_E d).ker) (q : higmanVCCommon_Q d) : Commute z q := by
  obtain ⟨r, rfl⟩ := higmanVCTreeNF_mk_surjective d z
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  exact higmanVCCommon_ker_central hd
    (MonoidHom.mem_ker.mpr ((higmanVCTreeNF_E_mk d r).symm.trans (MonoidHom.mem_ker.mp hz))) g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_central

/-- The generator `(c, c')` conjugates the letter `(c x, c y)` into `(c' x, c' y)`. -/
theorem higSw_conj_letter {d : ℕ} {c c' : List (Fin d)} (hcc : ¬ c <+: c') (hcc' : ¬ c' <+: c)
    (x y : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (c, c')) *
        higmanVCCommon_mk d (FreeGroup.of (c ++ x, c ++ y)) *
        (higmanVCCommon_mk d (FreeGroup.of (c, c')))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (c' ++ x, c' ++ y)) := by
  by_cases h : ¬ x <+: y ∧ ¬ y <+: x
  · have hr := higmanVCCommon_mk_rel (higmanVCCommon_conj_mem hcc hcc'
      ((mapsCone_coneSwap_left hcc hcc').append x) ((mapsCone_coneSwap_left hcc hcc').append y)
      (higSw_nprefix c h.1) (higSw_nprefix c h.2) (higSw_nprefix c' h.1) (higSw_nprefix c' h.2))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hr
    exact mul_inv_eq_one.mp hr
  · have h1 : ¬ (¬ c ++ x <+: c ++ y ∧ ¬ c ++ y <+: c ++ x) := fun h' =>
      h ((higSw_incomp_iff c x y).mp h')
    have h2 : ¬ (¬ c' ++ x <+: c' ++ y ∧ ¬ c' ++ y <+: c' ++ x) := fun h' =>
      h ((higSw_incomp_iff c' x y).mp h')
    rw [higmanVCCommon_mk_comparable h1, higmanVCCommon_mk_comparable h2, mul_one,
      mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_conj_letter

/-- **Conjugating prefixes.**  For incomparable `c`, `c'`, `(c, c') φ_c(q) (c, c')⁻¹ = φ_{c'}(q)`
for every `q ∈ Q`. -/
theorem higSw_conj_phi {d : ℕ} {c c' : List (Fin d)} (hcc : ¬ c <+: c') (hcc' : ¬ c' <+: c)
    (q : higmanVCCommon_Q d) :
    higmanVCCommon_mk d (FreeGroup.of (c, c')) * higSw_phi d c q *
        (higmanVCCommon_mk d (FreeGroup.of (c, c')))⁻¹ = higSw_phi d c' q := by
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  induction g using FreeGroup.induction_on with
  | C1 => simp only [map_one, mul_one, mul_inv_cancel]
  | of p =>
    obtain ⟨x, y⟩ := p
    rw [higSw_phi_gen, higSw_phi_gen]
    exact higSw_conj_letter hcc hcc' x y
  | inv_of p ih =>
    simp only [map_inv]
    rw [← ih]
    group
  | mul g₁ g₂ ih₁ ih₂ =>
    simp only [map_mul]
    rw [← ih₁, ← ih₂]
    group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_conj_phi

/-- **Independence, incomparable case.**  For `z ∈ Z` and incomparable `c`, `c'`,
`φ_c z = φ_{c'} z`. -/
theorem higSw_phi_ker_indep_incomp {d : ℕ} (hd : 1 < d) {c c' : List (Fin d)}
    (hcc : ¬ c <+: c') (hcc' : ¬ c' <+: c) {z : higmanVCCommon_Q d}
    (hz : z ∈ (higmanVCTreeNF_E d).ker) : higSw_phi d c z = higSw_phi d c' z :=
  ((higSw_central hd (higSw_phi_ker c hz)
      (higmanVCCommon_mk d (FreeGroup.of (c, c')))).symm.mul_inv_cancel).symm.trans
    (higSw_conj_phi hcc hcc' z)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_phi_ker_indep_incomp

/-- Words with distinct first letters are incomparable. -/
theorem higSw_not_prefix_cons {d : ℕ} {a b : Fin d} (h : a ≠ b) (l l' : List (Fin d)) :
    ¬ a :: l <+: b :: l' :=
  fun h' => h (List.cons_prefix_cons.mp h').1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_not_prefix_cons
