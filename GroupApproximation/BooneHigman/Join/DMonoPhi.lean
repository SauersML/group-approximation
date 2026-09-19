import GroupApproximation.BooneHigman.Join.DFaith
import GroupApproximation.BooneHigman.Join.DOrder

/-!
# The lift of `F_{n+2}` acts monotonically (lane bh-pal-met-join)

`RLt` is the lexicographic order on the ray `ℕ × Cantor`.  `up` is an order embedding
(`dlt_up`), Brown's generators on the ray are monotone (`rayR_mono`), and so is all of
`theta` (`theta_mono`).  The stream `t t t ⋯` is the maximum and lies off the image of `up`,
so every `E(psiD g)` fixes it.  Hence `E(q)` is monotone for `q ∈ PhiD n` (`dmono_of_mem`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope
open GroupApproximation.ThompsonOre GroupApproximation.HigmanThompson

variable {n : ℕ}

/-- The lexicographic order on the ray. -/
def RLt (p p' : ℕ × Cantor (Fin (n + 2))) : Prop := p.1 < p'.1 ∨ (p.1 = p'.1 ∧ DLt p.2 p'.2)

#audit_axioms GroupApproximation.BooneHigman.Join.RLt

theorem rlt_irrefl (p : ℕ × Cantor (Fin (n + 2))) : ¬ RLt p p := by
  rintro (h | ⟨-, h⟩)
  · exact lt_irrefl _ h
  · exact dlt_irrefl _ h

#audit_axioms GroupApproximation.BooneHigman.Join.rlt_irrefl

theorem rlt_trans {p q r : ℕ × Cantor (Fin (n + 2))} (h1 : RLt p q) (h2 : RLt q r) : RLt p r := by
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨e1.trans e2, dlt_trans h1 h2⟩

#audit_axioms GroupApproximation.BooneHigman.Join.rlt_trans

theorem rlt_total {p q : ℕ × Cantor (Fin (n + 2))} (h : p ≠ q) : RLt p q ∨ RLt q p := by
  rcases lt_trichotomy p.1 q.1 with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · have h2 : p.2 ≠ q.2 := fun e => h (Prod.ext h1 e)
    rcases dlt_total h2 with h3 | h3
    · exact Or.inl (Or.inr ⟨h1, h3⟩)
    · exact Or.inr (Or.inr ⟨h1.symm, h3⟩)
  · exact Or.inr (Or.inl h1)

#audit_axioms GroupApproximation.BooneHigman.Join.rlt_total

/-- `g` preserves the order of the ray. -/
def RMono (g : Equiv.Perm (ℕ × Cantor (Fin (n + 2)))) : Prop :=
  ∀ p q, RLt p q → RLt (g p) (g q)

#audit_axioms GroupApproximation.BooneHigman.Join.RMono

theorem RMono.inv {g : Equiv.Perm (ℕ × Cantor (Fin (n + 2)))} (hg : RMono g) : RMono g⁻¹ := by
  intro p q h
  have hne : g⁻¹ p ≠ g⁻¹ q := fun e => rlt_irrefl q (by rwa [(g⁻¹).injective e] at h)
  rcases rlt_total hne with h' | h'
  · exact h'
  · have h'' := hg _ _ h'
    simp only [Equiv.Perm.apply_inv_self] at h''
    exact (rlt_irrefl _ (rlt_trans h h'')).elim

#audit_axioms GroupApproximation.BooneHigman.Join.RMono.inv

theorem prepend_single_dlt {a b : Fin (n + 2)} (hab : a < b) (y z : Cantor (Fin (n + 2))) :
    DLt (prepend [a] y) (prepend [b] z) := by
  have h := dbefore_of [] [] [] hab y z
  simpa using h

#audit_axioms GroupApproximation.BooneHigman.Join.prepend_single_dlt

theorem rayR_mono (N : ℕ) : RMono (rayR n N) := by
  rintro ⟨M, w⟩ ⟨M', w'⟩ h
  dsimp only [RLt] at h ⊢
  simp only [rayR_apply]
  have key : ∀ K v, K ≥ N → (rayF n N (K, v)).1 ≥ N := by
    intro K v hK
    rcases Nat.lt_or_ge (N + n + 1) K with h2 | h2
    · rw [rayF_gt v h2]; dsimp only; omega
    · rw [rayF_mid v hK h2]
      all_goals exact le_refl N
  rcases h with h | ⟨he, h⟩
  · rcases Nat.lt_or_ge M N with h1 | h1
    · rw [rayF_lt w h1]
      rcases Nat.lt_or_ge M' N with h1' | h1'
      · rw [rayF_lt w' h1']; exact Or.inl h
      · exact Or.inl (lt_of_lt_of_le h1 (key M' w' h1'))
    · rcases Nat.lt_or_ge (N + n + 1) M with h2 | h2
      · rw [rayF_gt w h2, rayF_gt w' (by omega)]; exact Or.inl (by dsimp only; omega)
      · rw [rayF_mid w h1 h2]
        rcases Nat.lt_or_ge (N + n + 1) M' with h2' | h2'
        · rw [rayF_gt w' h2']; exact Or.inl (by dsimp only; omega)
        · rw [rayF_mid w' (by omega) h2']
          refine Or.inr ⟨rfl, prepend_single_dlt ?_ w w'⟩
          show (fc n (M - N)).val < (fc n (M' - N)).val
          rw [fc_val_of_lt (n := n) (i := M - N) (by omega),
            fc_val_of_lt (n := n) (i := M' - N) (by omega)]
          omega
  · cases he
    rcases Nat.lt_or_ge M N with h1 | h1
    · rw [rayF_lt w h1, rayF_lt w' h1]; exact Or.inr ⟨rfl, h⟩
    · rcases Nat.lt_or_ge (N + n + 1) M with h2 | h2
      · rw [rayF_gt w h2, rayF_gt w' h2]; exact Or.inr ⟨rfl, h⟩
      · rw [rayF_mid w h1 h2, rayF_mid w' h1 h2]
        exact Or.inr ⟨rfl, dlt_prepend _ h⟩

#audit_axioms GroupApproximation.BooneHigman.Join.rayR_mono

theorem theta_mono (g : BrownGroup n) : RMono (theta n g : Equiv.Perm _) := by
  have hg : g ∈ Subgroup.closure (Set.range (brownXd n)) := by
    rw [brownXd_closure]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨N, rfl⟩ := hx
    rw [theta_x]
    exact rayR_mono N
  | one => rw [map_one]; exact fun p q h => h
  | mul x y _ _ hx hy => rw [map_mul]; exact fun p q h => hx _ _ (hy _ _ h)
  | inv x _ hx => rw [map_inv]; exact RMono.inv hx

#audit_axioms GroupApproximation.BooneHigman.Join.theta_mono

theorem up_split (p : ℕ × Cantor (Fin (n + 2))) :
    ∃ q j, j < n + 1 ∧ up n p = prepend (List.replicate q (tl n) ++ [fc n j]) p.2 ∧
      p.1 = j + q * (n + 1) :=
  ⟨p.1 / (n + 1), p.1 % (n + 1), Nat.mod_lt _ (by omega), rfl,
    (Nat.mod_add_div' p.1 (n + 1)).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Join.up_split

/-- **`up` is an order embedding.** -/
theorem dlt_up {p p' : ℕ × Cantor (Fin (n + 2))} (h : RLt p p') : DLt (up n p) (up n p') := by
  obtain ⟨q, j, hj, e, hp⟩ := up_split p
  obtain ⟨q', j', hj', e', hp'⟩ := up_split p'
  rw [e, e']
  rcases h with h | ⟨h1, h⟩
  · rcases Nat.lt_or_ge q q' with hq | hq
    · obtain ⟨r, rfl⟩ : ∃ r, q' = q + 1 + r := ⟨q' - q - 1, by omega⟩
      have e2 : List.replicate (q + 1 + r) (tl n) ++ [fc n j'] =
          List.replicate q (tl n) ++ tl n :: (List.replicate r (tl n) ++ [fc n j']) := by
        rw [List.replicate_add, List.replicate_add, List.replicate_one]
        simp
      rw [e2]
      exact dbefore_of _ [] _ (show (fc n j).val < (tl n).val by
        rw [fc_val_of_lt (n := n) (i := j) (by omega), fc_val_of_lt (n := n) (i := n + 1)
          (by omega)]
        omega) _ _
    · have hq' : q = q' := by
        by_contra hne
        have : q' + 1 ≤ q := by omega
        have := Nat.mul_le_mul_right (n + 1) this
        rw [add_one_mul] at this
        omega
      subst hq'
      have hjj : j < j' := by omega
      exact dbefore_of _ [] [] (show (fc n j).val < (fc n j').val by
        rw [fc_val_of_lt (n := n) (i := j) (by omega), fc_val_of_lt (n := n) (i := j')
          (by omega)]
        exact hjj) _ _
  · have hq : q = q' ∧ j = j' := by
      have h2 : j + q * (n + 1) = j' + q' * (n + 1) := by rw [← hp, ← hp', h1]
      have h3 := congrArg (· / (n + 1)) h2
      have h4 := congrArg (· % (n + 1)) h2
      simp only [Nat.add_mul_div_right _ _ (show 0 < n + 1 by omega), Nat.div_eq_of_lt hj,
        Nat.div_eq_of_lt hj', Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj,
        Nat.mod_eq_of_lt hj'] at h3 h4
      exact ⟨h3, h4⟩
    obtain ⟨rfl, rfl⟩ := hq
    exact dlt_prepend _ h

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_up

/-- The stream `t t t ⋯`. -/
def tom (n : ℕ) : Cantor (Fin (n + 2)) := fun _ => tl n

#audit_axioms GroupApproximation.BooneHigman.Join.tom

theorem up_ne_tom (p : ℕ × Cantor (Fin (n + 2))) : up n p ≠ tom n := by
  obtain ⟨q, j, hj, e, -⟩ := up_split p
  rw [e, prepend_append]
  intro h
  have h2 := congrFun h q
  rw [prepend_of_length_le _ _ (by simp), List.length_replicate, Nat.sub_self,
    prepend_single_zero] at h2
  exact fc_ne (n := n) (i := j) (j := n + 1) (by omega) (by omega) (by omega) h2

#audit_axioms GroupApproximation.BooneHigman.Join.up_ne_tom

theorem le_tl (a : Fin (n + 2)) : a ≤ tl n := by
  show a.val ≤ (fc n (n + 1)).val
  rw [fc_val_of_lt (n := n) (i := n + 1) (by omega)]
  omega

#audit_axioms GroupApproximation.BooneHigman.Join.le_tl

theorem not_dlt_tom (z : Cantor (Fin (n + 2))) : ¬ DLt (tom n) z := by
  rintro ⟨k, -, h⟩
  exact absurd (le_tl (z k)) (not_le.mpr h)

#audit_axioms GroupApproximation.BooneHigman.Join.not_dlt_tom

/-- The first index where `z` is not `t`. -/
theorem exists_first_ne {z : Cantor (Fin (n + 2))} (h : z ≠ tom n) :
    ∃ k, (∀ i < k, z i = tl n) ∧ z k ≠ tl n := by
  classical
  have hex : ∃ k, z k ≠ tl n := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  exact ⟨Nat.find hex, fun i hi => by
    by_contra hc
    exact Nat.find_min hex hi hc, Nat.find_spec hex⟩

#audit_axioms GroupApproximation.BooneHigman.Join.exists_first_ne

theorem dlt_tom {z : Cantor (Fin (n + 2))} (h : z ≠ tom n) : DLt z (tom n) := by
  obtain ⟨k, hk, hne⟩ := exists_first_ne h
  exact ⟨k, hk, lt_of_le_of_ne (le_tl (z k)) hne⟩

#audit_axioms GroupApproximation.BooneHigman.Join.dlt_tom

theorem up_surj {z : Cantor (Fin (n + 2))} (h : z ≠ tom n) : ∃ p, up n p = z := by
  obtain ⟨k, hk, hne⟩ := exists_first_ne h
  have hv : (z k).val < n + 1 := by
    have h1 := le_tl (z k)
    have h2 : (z k).val ≠ (tl n).val := fun e => hne (Fin.ext e)
    have h3 : (tl n).val = n + 1 := fc_val_of_lt (n := n) (i := n + 1) (by omega)
    have h4 : (z k).val ≤ (tl n).val := h1
    omega
  refine ⟨((z k).val + k * (n + 1), dropN (k + 1) z), ?_⟩
  rw [up_mk k (z k).val hv, fc_val]
  have hl : (List.replicate k (tl n) ++ [z k]).length = k + 1 := by simp
  rw [← hl]
  refine prepend_dropN_of_isStreamPrefix _ _ fun i hi => ?_
  rw [hl] at hi
  rcases Nat.lt_or_ge i k with h1 | h1
  · rw [List.getElem_append_left (by simpa using h1), List.getElem_replicate]
    exact hk i h1
  · have hik : i = k := by omega
    subst hik
    rw [List.getElem_append_right (by simp)]
    simp

#audit_axioms GroupApproximation.BooneHigman.Join.up_surj

theorem psiD_fix_tom (g : BrownGroup n) : jperm (n + 2) (psiD n g) (tom n) = tom n := by
  by_contra h
  obtain ⟨p, hp⟩ := up_surj h
  have h2 := psiD_semi g (((theta n g : Equiv.Perm _))⁻¹ p)
  rw [Equiv.Perm.apply_inv_self, hp] at h2
  exact up_ne_tom _ ((jperm (n + 2) (psiD n g)).injective h2)

#audit_axioms GroupApproximation.BooneHigman.Join.psiD_fix_tom

/-- **The lift of `F_{n+2}` acts monotonically.** -/
theorem dmono_of_mem {q : higmanVCCommon_Q (n + 2)} (hq : q ∈ PhiD n) :
    DMono (jperm (n + 2) q) := by
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
  intro x y h
  by_cases hy : y = tom n
  · subst hy
    have hx : x ≠ tom n := fun e => by
      rw [e] at h
      exact dlt_irrefl _ h
    rw [psiD_fix_tom]
    refine dlt_tom fun e => hx ?_
    rw [← psiD_fix_tom g] at e
    exact (jperm (n + 2) (psiD n g)).injective e
  · by_cases hx : x = tom n
    · subst hx
      exact absurd h (not_dlt_tom y)
    · obtain ⟨p, rfl⟩ := up_surj hx
      obtain ⟨p', rfl⟩ := up_surj hy
      have hpp : RLt p p' := by
        by_cases e : p = p'
        · subst e
          exact absurd h (dlt_irrefl _)
        · rcases rlt_total e with h' | h'
          · exact h'
          · exact absurd (dlt_trans h (dlt_up h')) (dlt_irrefl _)
      rw [psiD_semi, psiD_semi]
      exact dlt_up (theta_mono g _ _ hpp)

#audit_axioms GroupApproximation.BooneHigman.Join.dmono_of_mem

end GroupApproximation.BooneHigman.Join
