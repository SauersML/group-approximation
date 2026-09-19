import GroupApproximation.BooneHigman.Join.DRel
import GroupApproximation.BooneHigman.Join.DRay

/-!
# The generators of `PhiD` act on the ray as Brown's generators (lane bh-pal-met-join)

`xgen_semi`: `E(x_N) (up p) = up (rayR N p)`.  The proof follows the cells:
* cells of level below that of `N` are fixed;
* at the level of `N`, the cone maps of `A_a` (`Arot_maps`) give the three pieces of `rayR`;
* at levels two or more above, `A_a` maps `[t, t] ↦ [t]`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

theorem up_mk (q j : ℕ) (hj : j < n + 1) (w : Cantor (Fin (n + 2))) :
    up n (j + q * (n + 1), w) = prepend (List.replicate q (tl n) ++ [fc n j]) w := by
  show prepend (List.replicate ((j + q * (n + 1)) / (n + 1)) (tl n) ++
    [fc n ((j + q * (n + 1)) % (n + 1))]) w = _
  rw [Nat.add_mul_div_right _ _ (show 0 < n + 1 by omega), Nat.div_eq_of_lt hj, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

#audit_axioms GroupApproximation.BooneHigman.Join.up_mk

theorem rep_inc_lt {X : Type*} {t c : X} (hc : c ≠ t) : ∀ q Q : ℕ, q < Q →
    ¬ List.replicate q t ++ [c] <+: List.replicate Q t ∧
      ¬ List.replicate Q t <+: List.replicate q t ++ [c]
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, Q + 1, _ => ⟨fun h => hc (List.cons_prefix_cons.mp h).1,
      fun h => hc (List.cons_prefix_cons.mp h).1.symm⟩
  | q + 1, Q + 1, h => by
    obtain ⟨h1, h2⟩ := rep_inc_lt hc q Q (by omega)
    exact ⟨fun h' => h1 (List.cons_prefix_cons.mp h').2,
      fun h' => h2 (List.cons_prefix_cons.mp h').2⟩

#audit_axioms GroupApproximation.BooneHigman.Join.rep_inc_lt

theorem prepend_app3 {X : Type*} (a b c : List X) (w : Cantor X) :
    prepend a (prepend b (prepend c w)) = prepend (a ++ (b ++ c)) w := by
  rw [prepend_append, prepend_append]

#audit_axioms GroupApproximation.BooneHigman.Join.prepend_app3

/-- **The generators act on the ray as Brown's generators.** -/
theorem xgen_semi (N : ℕ) (p : ℕ × Cantor (Fin (n + 2))) :
    jperm (n + 2) (xgen n N) (up n p) = up n (rayR n N p) := by
  obtain ⟨M, w⟩ := p
  obtain ⟨Q, a, ha, rfl⟩ : ∃ Q a, a < n + 1 ∧ N = a + Q * (n + 1) :=
    ⟨N / (n + 1), N % (n + 1), Nat.mod_lt _ (by omega), (Nat.mod_add_div' N (n + 1)).symm⟩
  obtain ⟨q, j, hj, rfl⟩ : ∃ q j, j < n + 1 ∧ M = j + q * (n + 1) :=
    ⟨M / (n + 1), M % (n + 1), Nat.mod_lt _ (by omega), (Nat.mod_add_div' M (n + 1)).symm⟩
  obtain ⟨fa, fb, fc', fd⟩ := Arot_maps (n := n) (j := a) (by omega)
  have hx : xgen n (a + Q * (n + 1)) = jPhi (n + 2) (List.replicate Q (tl n)) (Arot n a) := by
    rw [xgen_add, xgen_lt ha]
  rw [rayR_apply, hx, jperm_jPhi, up_mk q j hj]
  have hjt : fc n j ≠ tl n := fc_ne (by omega) (by omega) (by omega)
  rcases Nat.lt_or_ge q Q with hq | hq
  · -- a lower level: fixed
    have hle : (q + 1) * (n + 1) ≤ Q * (n + 1) := Nat.mul_le_mul_right (n + 1) hq
    rw [add_one_mul] at hle
    rw [localize_apply_of_not, rayF_lt w (by omega), up_mk q j hj]
    intro hp
    obtain ⟨h1, h2⟩ := rep_inc_lt hjt q Q hq
    rcases prefix_or_prefix_of_isStreamPrefix hp (isStreamPrefix_prepend _ w) with h | h
    · exact h2 h
    · exact h1 h
  obtain ⟨r, rfl⟩ : ∃ r, q = Q + r := ⟨q - Q, by omega⟩
  rw [List.replicate_add, List.append_assoc, prepend_append, localize_apply_prepend, Nat.add_mul]
  rcases r with _ | _ | r
  · -- the level of `N`
    simp only [List.replicate_zero, List.nil_append, Nat.zero_mul, Nat.add_zero]
    rcases Nat.lt_or_ge j a with hja | hja
    · rw [fa j hja w, rayF_lt w (by omega), up_mk Q j hj, prepend_append]
    · rw [fb j hja (by omega) w, rayF_mid w (by omega) (by omega),
        show j + Q * (n + 1) - (a + Q * (n + 1)) = j - a by omega, up_mk Q a ha, prepend_append]
      congr 1
      exact prepend_append [fc n a] [fc n (j - a)] w
  · -- one level above
    simp only [Nat.zero_add, Nat.one_mul, List.replicate_one, List.singleton_append]
    rcases Nat.lt_or_ge a j with hja | hja
    · rw [fd j (by omega) (by omega) w, rayF_gt w (by omega),
        show j + (Q * (n + 1) + (n + 1)) - (n + 1) = j + Q * (n + 1) by omega, up_mk Q j hj,
        prepend_append]
    · rw [fc' j hja w, rayF_mid w (by omega) (by omega),
        show j + (Q * (n + 1) + (n + 1)) - (a + Q * (n + 1)) = n + 1 - a + j by omega,
        up_mk Q a ha, prepend_append]
      congr 1
      exact prepend_append [fc n a] [fc n (n + 1 - a + j)] w
  · -- two or more levels above
    have htt : MapsCone (jperm (n + 2) (Arot n a)) [tl n, tl n] [tl n] :=
      fd (n + 1) (by omega) le_rfl
    have e1 : List.replicate (r + 1 + 1) (tl n) ++ [fc n j] =
        [tl n, tl n] ++ (List.replicate r (tl n) ++ [fc n j]) := by
      simp [List.replicate_succ]
    rw [e1, prepend_append, htt (prepend (List.replicate r (tl n) ++ [fc n j]) w),
      rayF_gt w (by simp only [Nat.add_mul, Nat.one_mul]; omega)]
    have e2 : j + (Q * (n + 1) + (r + 1 + 1) * (n + 1)) - (n + 1) =
        j + (Q + 1 + r) * (n + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    rw [e2, up_mk (Q + 1 + r) j hj, List.replicate_add, List.replicate_add, List.replicate_one,
      prepend_app3]
    simp [List.append_assoc]

#audit_axioms GroupApproximation.BooneHigman.Join.xgen_semi

end GroupApproximation.BooneHigman.Join
