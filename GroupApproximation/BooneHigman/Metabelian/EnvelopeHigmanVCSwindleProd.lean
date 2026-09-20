import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleDiag
import GroupApproximation.Meta.AxiomGuard

/-!
# What a product swindle forces (lane bh-hig-02)

This file is **not** a residual reduction of `HigmanVCStepBCoreStatement` or
`HigmanVCOrbitGapStatement`.  It records exactly what the natural "swindle" identity
`∏_{a} φ_[a](z) = z` gives for `z ∈ Z = ker Ē`, combined with prefix independence
(`higSw_phi_ker_indep`) and fixedness (`higSw_phi_ker_fixed`): only the torsion bound
`z ^ (d - 1) = 1` (`higSw_prod_forcing`).  For `d = 2` this is `z = 1`
(`higSw_prod_forcing_two`); for `d ≥ 3` it does not force `z = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Product forcing.**  For `1 < d` and `z ∈ Z`, the identity `∏_{a} φ_[a](z) = z`
forces `z ^ (d - 1) = 1`. -/
theorem higSw_prod_forcing {d : ℕ} (hd : 1 < d) {z : higmanVCCommon_Q d}
    (hz : z ∈ (higmanVCTreeNF_E d).ker)
    (hprod : higSw_diag d z = z) :
    z ^ (d - 1) = 1 := by
  change ((List.finRange d).map fun a => higSw_phi d [a] z).prod = z at hprod
  have a0 : Fin d := ⟨0, lt_trans Nat.zero_lt_one hd⟩
  have hall : ∀ a : Fin d, higSw_phi d [a] z = higSw_phi d [a0] z := fun a =>
    higSw_phi_ker_indep hd (List.cons_ne_nil a []) (List.cons_ne_nil a0 []) hz
  have hmap : (List.finRange d).map (fun a => higSw_phi d [a] z) =
      (List.finRange d).map (fun _ => higSw_phi d [a0] z) :=
    List.map_congr_left fun a _ => hall a
  rw [hmap, List.map_const', List.prod_replicate, List.length_finRange] at hprod
  have hfix := higSw_phi_ker_fixed hd (List.cons_ne_nil a0 []) (List.cons_ne_nil a0 []) hz
  have h1 := congrArg (higSw_phi d [a0]) hprod
  rw [map_pow, hfix] at h1
  have hw : higSw_phi d [a0] z = z := h1.symm.trans hprod
  rw [hw] at hprod
  have h3 : z ^ (d - 1) * z = 1 * z := by
    rw [← pow_succ, Nat.sub_add_cancel hd.le, one_mul, hprod]
  exact mul_right_cancel h3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_prod_forcing

/-- For `d = 2` the product identity does force `z = 1`. -/
theorem higSw_prod_forcing_two {z : higmanVCCommon_Q 2}
    (hz : z ∈ (higmanVCTreeNF_E 2).ker)
    (hprod : higSw_diag 2 z = z) : z = 1 := by
  have h := higSw_prod_forcing Nat.one_lt_two hz hprod
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_prod_forcing_two

end GroupApproximation.BooneHigman.Metabelian.Envelope
