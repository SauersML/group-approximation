import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWitPivotLen
import GroupApproximation.Meta.AxiomGuard

/-!
# The kernel step of antichain pivot closure (lane bh-met-77p)

Here we prove the step that pivot closure (iii) leaves open.  Let `C` be a finite antichain
and `h ∈ H_C`.  If `E h ∈ E(U)`, then `h ∈ U`.

* `higmanVCTreeNFWitPivot_decomp`: a length-preserving permutation of `C` is a product of
  transpositions of equal-length words.  The corresponding word in `Q` lies in `U`, since each
  letter is balanced.
* `higmanVCTreeNFWitPivot_mem_U`: write `h = mk (ι_C r)`.  Its permutation `σ` preserves lengths
  (`higmanVCTreeNFWitPivot_len`).  Decompose `σ` as `r'` with `mk (ι_C r') ∈ U`.  Then `r r'⁻¹`
  has trivial transposition image, so the transposition presentation
  (`higmanVCAll_lift_eq_one`) kills its class, and `h = mk (ι_C r') ∈ U`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higmanVCTreeNFWitPivot_swap_len {d : ℕ} {C : Finset (List (Fin d))} {x y : ↥C}
    (hxy : x.1.length = y.1.length) (z : ↥C) : (Equiv.swap x y z).1.length = z.1.length := by
  by_cases hzx : z = x
  · rw [hzx, Equiv.swap_apply_left, hxy]
  · by_cases hzy : z = y
    · rw [hzy, Equiv.swap_apply_right, hxy]
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_swap_len

/-- A length-preserving permutation of `C` comes from a balanced word. -/
theorem higmanVCTreeNFWitPivot_decomp {d : ℕ} {C : Finset (List (Fin d))} :
    ∀ (k : ℕ) (σ : Equiv.Perm ↥C), σ.support.card ≤ k →
      (∀ c : ↥C, (σ c).1.length = c.1.length) →
        ∃ r : FreeGroup (↥C × ↥C),
          FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r = σ ∧
            higmanVCCommon_mk d (higmanVCAll_iota C r) ∈ higmanVCTreeNF_U d := by
  intro k
  induction k with
  | zero =>
    intro σ hk _
    have hσ : σ = 1 :=
      Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hk))
    subst hσ
    refine ⟨1, map_one _, ?_⟩
    rw [map_one, map_one]
    exact (higmanVCTreeNF_U d).one_mem
  | succ k ih =>
    intro σ hk hlen
    by_cases hσ : σ = 1
    · subst hσ
      refine ⟨1, map_one _, ?_⟩
      rw [map_one, map_one]
      exact (higmanVCTreeNF_U d).one_mem
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
        by_contra hne
        push Not at hne
        exact hσ (Equiv.ext fun y => (hne y).trans (Equiv.Perm.one_apply y).symm)
      have hτ : (Equiv.swap x (σ x) * σ).support.card ≤ k := by
        have := Equiv.Perm.card_support_swap_mul hx
        omega
      have hxl : x.1.length = (σ x).1.length := (hlen x).symm
      obtain ⟨r, hr, hU⟩ := ih _ hτ fun c => by
        rw [Equiv.Perm.mul_apply, higmanVCTreeNFWitPivot_swap_len hxl, hlen]
      refine ⟨FreeGroup.of (x, σ x) * r, ?_, ?_⟩
      · rw [map_mul, hr, FreeGroup.lift_apply_of]
        exact Equiv.swap_mul_self_mul x (σ x) σ
      · simp only [map_mul, higmanVCAll_iota_of]
        exact (higmanVCTreeNF_U d).mul_mem (higmanVCTreeNF_letter_mem hxl) hU

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_decomp

/-- **The kernel step.**  An antichain element with a balanced `E`-image is balanced. -/
theorem higmanVCTreeNFWitPivot_mem_U {d : ℕ} (hd : 1 < d) {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) {h β : higmanVCCommon_Q d}
    (hh : h ∈ higmanVCTreeNFWitPivot_H d C) (hβ : β ∈ higmanVCTreeNF_U d)
    (e : higmanVCTreeNF_E d h = higmanVCTreeNF_E d β) : h ∈ higmanVCTreeNF_U d := by
  obtain ⟨r, rfl⟩ := higmanVCTreeNFWitPivot_mem_H.mp hh
  obtain ⟨r', hr', hU⟩ := higmanVCTreeNFWitPivot_decomp _
    (FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) r) le_rfl
    (higmanVCTreeNFWitPivot_len hd hC r hβ e)
  have h1 : FreeGroup.lift (fun p : ↥C × ↥C => Equiv.swap p.1 p.2) (r * r'⁻¹) = 1 := by
    rw [map_mul, map_inv, hr', mul_inv_cancel]
  have h2 := higmanVCAll_lift_eq_one (higmanVCAll_gen d C) higmanVCAll_gen_self
    higmanVCAll_gen_sq (higmanVCAll_gen_conj hC) (r * r'⁻¹) h1
  have h3 : higmanVCCommon_mk d (higmanVCAll_iota C (r * r'⁻¹)) = 1 := by
    rw [higmanVCCommon_mk, higmanVCAll_mk_iota]
    exact h2
  simp only [map_mul, map_inv] at h3
  rw [mul_inv_eq_one.mp h3]
  exact hU

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_mem_U

end GroupApproximation.BooneHigman.Metabelian.Envelope
