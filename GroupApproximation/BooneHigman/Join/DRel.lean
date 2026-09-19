import GroupApproximation.BooneHigman.Join.DGen
import GroupApproximation.ThompsonOre.NormalFormDBrown

/-!
# Brown's relations in `Q`, and the lift of `F_{n+2}` (lane bh-pal-met-join)

`xgen n N = jPhi (t^q) (A_a)` for `N = q (n+1) + a`, `a ≤ n`.  These are Brown's generators
of `F_{n+2,∞}`.  The shift by `n + 1` is the prefix lift at `t` (`xgen_add`).

* `xgen_rel`: `x_j x_i = x_i x_{j+n+1}` for `i < j`.  This reduces to `A_a` conjugating
  `jPhi [t] x_j` back to `x_j`, which is rigid, because `A_a` maps `[t, m] ↦ [m]` for `m > a`.
* `psiD := ThompsonOre.brownLift (xgen n) xgen_rel : BrownGroup n →* Q`, and `PhiD` is its range.
* `jPhi_t_mem`: the prefix lift at `t` maps `PhiD` into itself.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- Brown's generators `x_N` of `F_{n+2,∞}` in `Q`. -/
noncomputable def xgen (n N : ℕ) : higmanVCCommon_Q (n + 2) :=
  jPhi (n + 2) (List.replicate (N / (n + 1)) (tl n)) (Arot n (N % (n + 1)))

#audit_axioms GroupApproximation.BooneHigman.Join.xgen

theorem xgen_add (N q : ℕ) :
    xgen n (N + q * (n + 1)) = jPhi (n + 2) (List.replicate q (tl n)) (xgen n N) := by
  unfold xgen
  rw [jPhi_append, ← List.replicate_add, Nat.add_mul_div_right _ _ (show 0 < n + 1 by omega),
    Nat.add_mul_mod_self_right, Nat.add_comm (N / (n + 1)) q]

#audit_axioms GroupApproximation.BooneHigman.Join.xgen_add

theorem xgen_lt {N : ℕ} (h : N < n + 1) : xgen n N = Arot n N := by
  unfold xgen
  rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, List.replicate_zero, jPhi_nil']

#audit_axioms GroupApproximation.BooneHigman.Join.xgen_lt

theorem xgen_succ_shift (N : ℕ) : xgen n (N + (n + 1)) = jPhi (n + 2) [tl n] (xgen n N) := by
  have h := xgen_add (n := n) N 1
  rwa [Nat.one_mul, List.replicate_one] at h

#audit_axioms GroupApproximation.BooneHigman.Join.xgen_succ_shift

/-- `A_a` conjugates `t A_j` back to `A_j`, for `a < j`. -/
theorem Arot_conj_Arot {a : ℕ} (ha : a ≤ n) : ∀ r j : ℕ, j + r = n + 1 → a < j →
    Arot n a * jPhi (n + 2) [tl n] (Arot n j) * (Arot n a)⁻¹ = Arot n j
  | 0, j, hj, _ => by
    rw [Arot_of_gt (show n < j by omega), map_one, mul_one, mul_inv_cancel]
  | r + 1, j, hj, haj => by
    obtain ⟨-, -, -, hd⟩ := Arot_maps (n := n) (j := a) (by omega)
    have hx : ¬ [fc n j] <+: [fc n (j + 1)] := fc_inc (by omega) (by omega) (by omega)
    have hy : ¬ [fc n (j + 1)] <+: [fc n j] := fc_inc (by omega) (by omega) (by omega)
    have ih := Arot_conj_Arot ha r (j + 1) (by omega) (by omega)
    rw [Arot_of_le (show j ≤ n by omega), map_mul, jPhi_Prot]
    have hx1 : ¬ [tl n] ++ [fc n j] <+: [tl n] ++ [fc n (j + 1)] :=
      dinc_cons [tl n] (fc_ne (by omega) (by omega) (by omega)) [] []
    have hy1 : ¬ [tl n] ++ [fc n (j + 1)] <+: [tl n] ++ [fc n j] :=
      dinc_cons [tl n] (fc_ne (by omega) (by omega) (by omega)) [] []
    have hp := Prot_conj hx1 hy1 (Arot n a) (hd j (by omega) (by omega))
      (hd (j + 1) (by omega) (by omega))
    have e : ∀ u v : higmanVCCommon_Q (n + 2),
        Arot n a * (u * v) * (Arot n a)⁻¹ =
          (Arot n a * u * (Arot n a)⁻¹) * (Arot n a * v * (Arot n a)⁻¹) := fun u v => by group
    rw [e, hp, ih]
    all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.Arot_conj_Arot

/-- The core relation, for `a ≤ n < …` and `a < j`. -/
theorem xgen_conj_core {a j : ℕ} (ha : a < n + 1) (haj : a < j) :
    xgen n a * xgen n (j + (n + 1)) * (xgen n a)⁻¹ = xgen n j := by
  obtain ⟨-, -, -, hd⟩ := Arot_maps (n := n) (j := a) (by omega)
  rw [xgen_lt ha, xgen_succ_shift]
  rcases Nat.lt_or_ge j (n + 1) with hj | hj
  · rw [xgen_lt hj]
    exact Arot_conj_Arot (by omega) (n + 1 - j) j (by omega) haj
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + (n + 1) := ⟨j - (n + 1), by omega⟩
    rw [xgen_succ_shift, jPhi_append]
    have htt : MapsCone (jperm (n + 2) (Arot n a)) ([tl n] ++ [tl n]) [tl n] :=
      hd (n + 1) (by omega) le_rfl
    exact rcl_phi (dn2 n) (Arot n a) htt _

#audit_axioms GroupApproximation.BooneHigman.Join.xgen_conj_core

/-- **Brown's relations**: `x_j x_i = x_i x_{j + n + 1}` for `i < j`. -/
theorem xgen_rel : ∀ i j : ℕ, i < j → xgen n j * xgen n i = xgen n i * xgen n (j + (n + 1)) := by
  intro i j hij
  obtain ⟨q, a, ha, rfl⟩ : ∃ q a, a < n + 1 ∧ i = a + q * (n + 1) :=
    ⟨i / (n + 1), i % (n + 1), Nat.mod_lt _ (by omega), by
      rw [Nat.mul_comm]; exact (Nat.mod_add_div i (n + 1)).symm⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + q * (n + 1) := ⟨j - q * (n + 1), by omega⟩
  have hc := xgen_conj_core (n := n) ha (show a < j' by omega)
  have e1 : j' + q * (n + 1) + (n + 1) = (j' + (n + 1)) + q * (n + 1) := by omega
  rw [e1, xgen_add, xgen_add, xgen_add, ← map_mul, ← map_mul, ← hc, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Join.xgen_rel

/-- The lift of Brown's group `F_{n+2,∞}` to `Q`. -/
noncomputable def psiD (n : ℕ) :
    GroupApproximation.HigmanThompson.BrownGroup n →* higmanVCCommon_Q (n + 2) :=
  GroupApproximation.ThompsonOre.brownLift (xgen n) xgen_rel

#audit_axioms GroupApproximation.BooneHigman.Join.psiD

/-- The lift of `F_{n+2}`: the range of `psiD`. -/
noncomputable def PhiD (n : ℕ) : Subgroup (higmanVCCommon_Q (n + 2)) := (psiD n).range

#audit_axioms GroupApproximation.BooneHigman.Join.PhiD

theorem xgen_mem (N : ℕ) : xgen n N ∈ PhiD n :=
  ⟨GroupApproximation.ThompsonOre.brownXd n N,
    GroupApproximation.ThompsonOre.brownLift_xd (xgen n) xgen_rel N⟩

#audit_axioms GroupApproximation.BooneHigman.Join.xgen_mem

theorem PhiD_eq_closure : PhiD n = Subgroup.closure (Set.range (xgen n)) := by
  rw [PhiD, MonoidHom.range_eq_map, ← GroupApproximation.ThompsonOre.brownXd_closure n,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext N
  exact GroupApproximation.ThompsonOre.brownLift_xd (xgen n) xgen_rel N

#audit_axioms GroupApproximation.BooneHigman.Join.PhiD_eq_closure

/-- A prefix lift maps `PhiD` into itself as soon as it maps the generators into it. -/
theorem jPhi_mem_of_gen (c : List (Fin (n + 2))) (h : ∀ N, jPhi (n + 2) c (xgen n N) ∈ PhiD n)
    {f : higmanVCCommon_Q (n + 2)} (hf : f ∈ PhiD n) : jPhi (n + 2) c f ∈ PhiD n := by
  rw [PhiD_eq_closure] at hf
  induction hf using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨N, rfl⟩ := hx
    exact h N
  | one => rw [map_one]; exact (PhiD n).one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact (PhiD n).mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact (PhiD n).inv_mem hx

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_mem_of_gen

/-- **The prefix lift at `t` maps `PhiD` into itself.** -/
theorem jPhi_t_mem {f : higmanVCCommon_Q (n + 2)} (hf : f ∈ PhiD n) :
    jPhi (n + 2) [tl n] f ∈ PhiD n :=
  jPhi_mem_of_gen [tl n] (fun N => by rw [← xgen_succ_shift]; exact xgen_mem _) hf

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_t_mem

theorem Arot_mem {j : ℕ} (h : j ≤ n) : Arot n j ∈ PhiD n := by
  rw [← xgen_lt (show j < n + 1 by omega)]
  exact xgen_mem j

#audit_axioms GroupApproximation.BooneHigman.Join.Arot_mem

theorem Prot_root_mem {i : ℕ} (h : i ≤ n) : Prot [fc n i] [fc n (i + 1)] ∈ PhiD n := by
  rw [Prot_root h]
  refine (PhiD n).mul_mem (Arot_mem h) ((PhiD n).inv_mem ?_)
  rcases Nat.lt_or_ge (i + 1) (n + 1) with h' | h'
  · exact Arot_mem (by omega)
  · rw [Arot_of_gt (by omega)]
    exact (PhiD n).one_mem

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_root_mem

end GroupApproximation.BooneHigman.Join
