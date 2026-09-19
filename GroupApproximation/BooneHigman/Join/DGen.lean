import GroupApproximation.BooneHigman.Join.DPent

/-!
# The root rotations `A_j` of `F_{n+2}` in `Q` (lane bh-pal-met-join)

`Arot n j = P(j, j+1) P(j+1, j+2) ⋯ P(n, n+1)` on one-letter words; `Arot n j = 1` for `j > n`.
These are Brown's generators `x_0, …, x_n` of `F_{n+2}` at the root.  `Arot_maps` gives their
cone maps:
* `[r] ↦ [r]` for `r < j`;
* `[r] ↦ [j, r - j]` for `j ≤ r ≤ n`;
* `[t, m] ↦ [j, n + 1 - j + m]` for `m ≤ j`;
* `[t, m] ↦ [m]` for `j < m ≤ n + 1`.
The last line says `A_j` translates the ray `t (j+1), …, t t` down by one level.  This is what
makes Brown's relations rigid conjugations (`DRel`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- `A_j = P(j, j+1) ⋯ P(n, n+1)`. -/
noncomputable def Arot (n : ℕ) (j : ℕ) : higmanVCCommon_Q (n + 2) :=
  if h : j ≤ n then Prot [fc n j] [fc n (j + 1)] * Arot n (j + 1) else 1
termination_by n + 1 - j

#audit_axioms GroupApproximation.BooneHigman.Join.Arot

theorem Arot_of_le {j : ℕ} (h : j ≤ n) :
    Arot n j = Prot [fc n j] [fc n (j + 1)] * Arot n (j + 1) := by
  conv_lhs => rw [Arot]
  rw [dif_pos h]

#audit_axioms GroupApproximation.BooneHigman.Join.Arot_of_le

theorem Arot_of_gt {j : ℕ} (h : n < j) : Arot n j = 1 := by
  rw [Arot, dif_neg (by omega)]

#audit_axioms GroupApproximation.BooneHigman.Join.Arot_of_gt

theorem pair_inc {X : Type*} {a b c : X} (hac : a ≠ c) : ¬ [a, b] <+: [c] := fun h =>
  hac (List.cons_prefix_cons.mp h).1

#audit_axioms GroupApproximation.BooneHigman.Join.pair_inc

theorem pair_inc' {X : Type*} {a b c : X} (hac : a ≠ c) : ¬ [c] <+: [a, b] := fun h =>
  hac (List.cons_prefix_cons.mp h).1.symm

#audit_axioms GroupApproximation.BooneHigman.Join.pair_inc'

/-- The cone maps of the root rotation `A_j`. -/
def ArotFacts (n j : ℕ) : Prop :=
  (∀ r, r < j → MapsCone (jperm (n + 2) (Arot n j)) [fc n r] [fc n r]) ∧
  (∀ r, j ≤ r → r ≤ n →
    MapsCone (jperm (n + 2) (Arot n j)) [fc n r] [fc n j, fc n (r - j)]) ∧
  (∀ m, m ≤ j →
    MapsCone (jperm (n + 2) (Arot n j)) [tl n, fc n m] [fc n j, fc n (n + 1 - j + m)]) ∧
  (∀ m, j + 1 ≤ m → m ≤ n + 1 → MapsCone (jperm (n + 2) (Arot n j)) [tl n, fc n m] [fc n m])

#audit_axioms GroupApproximation.BooneHigman.Join.ArotFacts

theorem Arot_maps_aux (n : ℕ) : ∀ r j : ℕ, j + r = n + 1 → ArotFacts n j
  | 0, j, hj => by
    have h1 : Arot n j = 1 := Arot_of_gt (by omega)
    refine ⟨fun r _ => ?_, fun r h h' => absurd h' (by omega), fun m hm => ?_,
      fun m h h' => absurd h' (by omega)⟩
    · rw [h1]
      exact dmc_one _
    · rw [h1, show n + 1 - j + m = m by omega, show j = n + 1 by omega]
      exact dmc_one _
  | r + 1, j, hj => by
    obtain ⟨ha, hb, hc, hd⟩ := Arot_maps_aux n r (j + 1) (by omega)
    have e := Arot_of_le (n := n) (j := j) (by omega)
    have hx : ¬ [fc n j] <+: [fc n (j + 1)] := fc_inc (by omega) (by omega) (by omega)
    have hy : ¬ [fc n (j + 1)] <+: [fc n j] := fc_inc (by omega) (by omega) (by omega)
    have hfixr : ∀ r', r' < n + 2 → r' ≠ j → r' ≠ j + 1 →
        MapsCone (jperm (n + 2) (Prot [fc n j] [fc n (j + 1)])) [fc n r'] [fc n r'] :=
      fun r' h h1 h2 => Prot_fix hx hy (fc_inc (by omega) h (Ne.symm h1)) (fc_inc h (by omega) h1)
        (fc_inc (by omega) h (Ne.symm h2)) (fc_inc h (by omega) h2)
    refine ⟨fun r' hr' => ?_, fun r' h1 h2 => ?_, fun m hm => ?_, fun m h1 h2 => ?_⟩
    · rw [e]
      exact dmc_mul (ha r' (by omega)) (hfixr r' (by omega) (by omega) (by omega))
    · rw [e]
      rcases Nat.lt_or_ge j r' with h | h
      · have hp := Prot_y hx hy (i := r' - (j + 1)) (by omega)
        rw [show r' - (j + 1) + 1 = r' - j by omega] at hp
        exact dmc_mul (hb r' (by omega) h2) hp
      · have hr : r' = j := by omega
        rw [hr, Nat.sub_self]
        exact dmc_mul (ha j (by omega)) (Prot_x hx hy)
    · rw [e]
      have hp := Prot_y hx hy (i := n + 1 - (j + 1) + m) (by omega)
      rw [show n + 1 - (j + 1) + m + 1 = n + 1 - j + m by omega] at hp
      exact dmc_mul (hc m (by omega)) hp
    · rw [e]
      rcases Nat.lt_or_ge (j + 1) m with h | h
      · have hf := hfixr m (by omega) (by omega) (by omega)
        exact dmc_mul (hd m (by omega) h2) hf
      · have hm : m = j + 1 := by omega
        rw [hm]
        have h0 := hc (j + 1) le_rfl
        rw [show n + 1 - (j + 1) + (j + 1) = n + 1 by omega] at h0
        exact dmc_mul h0 (Prot_yt hx hy)

#audit_axioms GroupApproximation.BooneHigman.Join.Arot_maps_aux

theorem Arot_maps {j : ℕ} (hj : j ≤ n + 1) : ArotFacts n j :=
  Arot_maps_aux n (n + 1 - j) j (by omega)

#audit_axioms GroupApproximation.BooneHigman.Join.Arot_maps

/-- The root rotation `P(i, i+1)` is `A_i A_{i+1}⁻¹`. -/
theorem Prot_root {i : ℕ} (h : i ≤ n) :
    Prot [fc n i] [fc n (i + 1)] = Arot n i * (Arot n (i + 1))⁻¹ := by
  rw [Arot_of_le h, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_root

/-- The prefix image of `A_j` is the product of the prefixed rotations. -/
theorem jPhi_Arot (q : List (Fin (n + 2))) : ∀ r j : ℕ, j + r = n + 1 →
    jPhi (n + 2) q (Arot n j) =
      ((List.range' j r).map fun m => Prot (q ++ [fc n m]) (q ++ [fc n (m + 1)])).prod
  | 0, j, hj => by
    rw [Arot_of_gt (by omega), map_one]
    all_goals rfl
  | r + 1, j, hj => by
    rw [Arot_of_le (by omega), map_mul, jPhi_Prot, jPhi_Arot q r (j + 1) (by omega),
      List.range'_succ, List.map_cons, List.prod_cons]

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_Arot

/-- **The pentagon, in terms of `A_0`**: `P(p, q 0) = P(p, q) · (q A_0)⁻¹`. -/
theorem Prot_zero {p q : List (Fin (n + 2))} (h1 : ¬ p <+: q) (h2 : ¬ q <+: p) :
    Prot p (q ++ [fc n 0]) = Prot p q * (jPhi (n + 2) q (Arot n 0))⁻¹ := by
  rw [mirror h1 h2, jPhi_Arot q (n + 1) 0 (by omega), ← List.range_eq_range',
    mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Join.Prot_zero

end GroupApproximation.BooneHigman.Join
