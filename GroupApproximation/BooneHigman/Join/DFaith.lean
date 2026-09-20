import GroupApproximation.BooneHigman.Join.DModel

/-!
# Faithfulness of the lift of `F_{n+2}` (lane bh-pal-met-join)

* `theta : BrownGroup n →* RW n` sends `x_N ↦ rayR N`; it commutes with the shifts
  (`theta_shift`) and so carries normal-form values to normal-form values (`theta_val`).
* `psiD_semi`: `E(psiD g) ∘ up = up ∘ theta g`.
* `PhiD_faithful`: an element of `PhiD n` with trivial evaluation is `1`.  Its Brown preimage
  has a normal form (`brownF_nf_exists`); by `psiD_semi` and injectivity of `up`, that form
  has value `1` in the ray model, so it is empty (`FdModel.eq_nil_of_val_eq_one`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope
open GroupApproximation.ThompsonOre GroupApproximation.HigmanThompson

variable {n : ℕ}

theorem rx_rel : ∀ i j : ℕ, i < j → rx n j * rx n i = rx n i * rx n (j + (n + 1)) :=
  fun i j h => Subtype.ext (rayR_rel i j h)

#audit_axioms GroupApproximation.BooneHigman.Join.rx_rel

/-- Brown's group acting on the ray. -/
noncomputable def theta (n : ℕ) : BrownGroup n →* ↥(RW n) := brownLift (rx n) rx_rel

#audit_axioms GroupApproximation.BooneHigman.Join.theta

theorem theta_x (N : ℕ) : theta n (brownXd n N) = rx n N := brownLift_xd (rx n) rx_rel N

#audit_axioms GroupApproximation.BooneHigman.Join.theta_x

theorem psiD_x (N : ℕ) : psiD n (brownXd n N) = xgen n N := brownLift_xd (xgen n) xgen_rel N

#audit_axioms GroupApproximation.BooneHigman.Join.psiD_x

theorem theta_shift (g : BrownGroup n) : theta n (brownShift n g) = rShift n (theta n g) := by
  have h : (theta n).comp (brownShift n) = (rShift n).comp (theta n) := by
    refine MonoidHom.eq_of_eqOn_dense (brownXd_closure n) ?_
    rintro _ ⟨N, rfl⟩
    show theta n (brownShift n (brownXd n N)) = rShift n (theta n (brownXd n N))
    rw [brownShift_x, theta_x, theta_x]
    exact Subtype.ext (shHom_rayR N).symm
  exact DFunLike.congr_fun h g

#audit_axioms GroupApproximation.BooneHigman.Join.theta_shift

theorem theta_val : ∀ l : List (ℕ × ℕ), theta n ((brownFdModel n).val l) = (rModel n).val l
  | [] => by simp only [FdModel.val_nil, map_one]
  | (a, b) :: r => by
    simp only [FdModel.val_cons, map_mul, map_inv, map_pow]
    have h0 : theta n ((brownFdModel n).x 0) = (rModel n).x 0 := theta_x 0
    have hs : theta n ((brownFdModel n).shift ((brownFdModel n).val r)) =
        (rModel n).shift ((rModel n).val r) := by
      show theta n (brownShift n _) = rShift n _
      rw [theta_shift, theta_val r]
    rw [h0, hs]

#audit_axioms GroupApproximation.BooneHigman.Join.theta_val

/-- **Semiconjugacy**: `E(psiD g) ∘ up = up ∘ theta g`. -/
theorem psiD_semi (g : BrownGroup n) (p : ℕ × Cantor (Fin (n + 2))) :
    jperm (n + 2) (psiD n g) (up n p) = up n ((theta n g : Equiv.Perm _) p) := by
  have hg : g ∈ Subgroup.closure (Set.range (brownXd n)) := by
    rw [brownXd_closure]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing p with
  | mem x hx =>
    obtain ⟨N, rfl⟩ := hx
    rw [psiD_x, theta_x]
    exact xgen_semi N p
  | one =>
    rw [map_one, map_one, jperm_one]
    all_goals rfl
  | mul x y _ _ hx hy =>
    rw [map_mul, jperm_mul, Equiv.Perm.mul_apply, hy, hx, map_mul]
    all_goals rfl
  | inv x _ hx =>
    have h := hx (((theta n x : Equiv.Perm _))⁻¹ p)
    rw [perm_apply_inv_self] at h
    rw [map_inv, jperm_inv, map_inv, Equiv.Perm.inv_eq_iff_eq, ← h]
    all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.psiD_semi

/-- **Faithfulness of the lift of `F_{n+2}`.** -/
theorem PhiD_faithful {q : higmanVCCommon_Q (n + 2)} (hq : q ∈ PhiD n)
    (h : jperm (n + 2) q = 1) : q = 1 := by
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
  obtain ⟨l, hl, rfl⟩ := brownF_nf_exists n g
  have ht : theta n ((brownFdModel n).val l) = 1 := by
    refine Subtype.ext (Equiv.ext fun p => up_injective (n := n) ?_)
    rw [← psiD_semi, h]
    all_goals rfl
  rw [theta_val] at ht
  rw [(rModel n).eq_nil_of_val_eq_one l hl ht, FdModel.val_nil, map_one]

#audit_axioms GroupApproximation.BooneHigman.Join.PhiD_faithful

end GroupApproximation.BooneHigman.Join
