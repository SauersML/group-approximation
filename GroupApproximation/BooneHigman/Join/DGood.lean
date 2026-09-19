import GroupApproximation.BooneHigman.Join.DRel

/-!
# Every prefix lift maps the lift of `F_{n+2}` into itself (lane bh-pal-met-join)

`GoodC n c`: `jPhi c` maps `PhiD n` into itself.

* `goodC_t`: true for `c = [t]`, since the shift by `n + 1` is the prefix lift at `t`.
* `rotk_mem`: the rotations `P(k m, k (m+1))` at a root letter `k ≤ n` lie in `PhiD`.  `A_k`
  carries them to rotations at the root (`k + m < n`), at `t` (`k + m > n`), or to the one
  rotation `P(n, t 0)` (`k + m = n`).  That last one is the pentagon (`Prot_zero`).
* `goodC_k`: true for `c = [k]`, by induction on the length of the `t`-tail.
* `goodC`: true for every word.
* `cross_mem`: the rotations `P(w i t^a, w (i+1) 0^b)` lie in `PhiD`.  These are the
  rotations at pairs of adjacent leaves of a tree.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- `jPhi c` maps `PhiD n` into itself. -/
def GoodC (n : ℕ) (c : List (Fin (n + 2))) : Prop :=
  ∀ f ∈ PhiD n, jPhi (n + 2) c f ∈ PhiD n

#audit_axioms GroupApproximation.BooneHigman.Join.GoodC

theorem goodC_nil : GoodC n [] := fun f hf => by
  rw [jPhi_nil']
  exact hf

#audit_axioms GroupApproximation.BooneHigman.Join.goodC_nil

theorem goodC_t : GoodC n [tl n] := fun _ hf => jPhi_t_mem hf

#audit_axioms GroupApproximation.BooneHigman.Join.goodC_t

theorem goodC_append {c c' : List (Fin (n + 2))} (h : GoodC n c) (h' : GoodC n c') :
    GoodC n (c ++ c') := fun f hf => by
  rw [← jPhi_append]
  exact h _ (h' f hf)

#audit_axioms GroupApproximation.BooneHigman.Join.goodC_append

theorem conj_mem {g f : higmanVCCommon_Q (n + 2)} (hg : g ∈ PhiD n) (hf : f ∈ PhiD n) :
    g * f * g⁻¹ ∈ PhiD n :=
  (PhiD n).mul_mem ((PhiD n).mul_mem hg hf) ((PhiD n).inv_mem hg)

#audit_axioms GroupApproximation.BooneHigman.Join.conj_mem

theorem cons_inc {X : Type*} {a b : X} (hab : a ≠ b) (u v : List X) : ¬ (a :: u) <+: (b :: v) :=
  fun h => hab (List.cons_prefix_cons.mp h).1

#audit_axioms GroupApproximation.BooneHigman.Join.cons_inc

/-- **The rotations at a root letter `k ≤ n`.** -/
theorem rotk_mem {k m : ℕ} (hk : k ≤ n) (hm : m ≤ n) :
    Prot [fc n k, fc n m] [fc n k, fc n (m + 1)] ∈ PhiD n := by
  obtain ⟨-, hb, hc, -⟩ := Arot_maps (n := n) (j := k) (by omega)
  have hg := Arot_mem (n := n) hk
  rcases Nat.lt_or_ge (k + m) n with h | h
  · -- a root rotation
    have h1 := hb (k + m) (by omega) (by omega)
    have h2 := hb (k + m + 1) (by omega) (by omega)
    rw [show k + m - k = m by omega] at h1
    rw [show k + m + 1 - k = m + 1 by omega] at h2
    rw [← Prot_conj (fc_inc (by omega) (by omega) (by omega))
      (fc_inc (by omega) (by omega) (by omega)) (Arot n k) h1 h2]
    exact conj_mem hg (Prot_root_mem (by omega))
  rcases Nat.lt_or_ge n (k + m) with h' | h'
  · -- a rotation at `t`
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + (n + 1 - k) := ⟨m - (n + 1 - k), by omega⟩
    have h1 := hc m' (by omega)
    have h2 := hc (m' + 1) (by omega)
    rw [show n + 1 - k + m' = m' + (n + 1 - k) by omega] at h1
    rw [show n + 1 - k + (m' + 1) = m' + (n + 1 - k) + 1 by omega] at h2
    have hx1 : ¬ [tl n] ++ [fc n m'] <+: [tl n] ++ [fc n (m' + 1)] :=
      dinc_cons [tl n] (fc_ne (by omega) (by omega) (by omega)) [] []
    have hy1 : ¬ [tl n] ++ [fc n (m' + 1)] <+: [tl n] ++ [fc n m'] :=
      dinc_cons [tl n] (fc_ne (by omega) (by omega) (by omega)) [] []
    rw [← Prot_conj hx1 hy1 (Arot n k) h1 h2]
    refine conj_mem hg ?_
    rw [← jPhi_Prot]
    exact jPhi_t_mem (Prot_root_mem (by omega))
  · -- the pentagon rotation `P(n, t 0)`
    have hkm : m = n - k := by omega
    subst hkm
    have h1 := hb n hk le_rfl
    have h2 := hc 0 (Nat.zero_le k)
    rw [show n + 1 - k + 0 = n - k + 1 by omega] at h2
    have hne : fc n n ≠ tl n := fc_ne (by omega) (by omega) (by omega)
    have hx1 : ¬ [fc n n] <+: [tl n, fc n 0] := cons_inc hne [] [fc n 0]
    have hy1 : ¬ [tl n, fc n 0] <+: [fc n n] := cons_inc hne.symm [fc n 0] []
    rw [← Prot_conj hx1 hy1 (Arot n k) h1 h2]
    refine conj_mem hg ?_
    have hz : Prot [fc n n] ([tl n] ++ [fc n 0]) ∈ PhiD n := by
      rw [Prot_zero (sing_inc hne) (sing_inc hne.symm)]
      exact (PhiD n).mul_mem (Prot_root_mem (i := n) le_rfl)
        ((PhiD n).inv_mem (jPhi_t_mem (Arot_mem (Nat.zero_le n))))
    exact hz

#audit_axioms GroupApproximation.BooneHigman.Join.rotk_mem

/-- `jPhi [k]` maps `PhiD` into itself, for a root letter `k ≤ n`. -/
theorem goodC_k {k : ℕ} (hk : k ≤ n) : GoodC n [fc n k] := by
  have hc := (Arot_maps (n := n) (j := k) (by omega)).2.2.1
  have hkt : MapsCone (jperm (n + 2) (Arot n k)) [tl n, fc n k] [fc n k, tl n] := by
    have h := hc k le_rfl
    rw [show n + 1 - k + k = n + 1 by omega] at h
    exact h
  have key : ∀ q a, a ≤ n + 1 →
      jPhi (n + 2) ([fc n k] ++ List.replicate q (tl n)) (Arot n a) ∈ PhiD n := by
    intro q
    induction q with
    | zero =>
      intro a ha
      rw [List.replicate_zero, List.append_nil, jPhi_Arot [fc n k] (n + 1 - a) a (by omega)]
      refine Subgroup.list_prod_mem _ ?_
      intro x hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      have hm' : m ≤ n := by
        rw [List.mem_range'_1] at hm
        omega
      exact rotk_mem hk hm'
    | succ q ih =>
      intro a ha
      have e : [fc n k] ++ List.replicate (q + 1) (tl n) =
          [fc n k, tl n] ++ List.replicate q (tl n) := by
        rw [List.replicate_succ]
        all_goals rfl
      rw [e, ← rcl_phi (dn2 n) (Arot n k) (hkt.append (List.replicate q (tl n)))]
      refine conj_mem (Arot_mem hk) ?_
      have e2 : [tl n, fc n k] ++ List.replicate q (tl n) =
          [tl n] ++ ([fc n k] ++ List.replicate q (tl n)) := rfl
      rw [e2, ← jPhi_append]
      exact jPhi_t_mem (ih a ha)
  refine fun f hf => jPhi_mem_of_gen _ (fun N => ?_) hf
  unfold xgen
  rw [jPhi_append]
  exact key _ _ (by have := Nat.mod_lt N (show 0 < n + 1 by omega); omega)

#audit_axioms GroupApproximation.BooneHigman.Join.goodC_k

/-- **Every prefix lift maps `PhiD` into itself.** -/
theorem goodC : ∀ c : List (Fin (n + 2)), GoodC n c
  | [] => goodC_nil
  | a :: c => by
    have ha : GoodC n [a] := by
      rcases Nat.lt_or_ge a.val (n + 1) with h | h
      · rw [← fc_val a]
        exact goodC_k (by omega)
      · have e : a = tl n := Fin.ext (by
          have := a.isLt
          rw [fc_val_of_lt (n := n) (i := n + 1) (by omega)]
          omega)
        rw [e]
        exact goodC_t
    exact goodC_append (c := [a]) ha (goodC c)

#audit_axioms GroupApproximation.BooneHigman.Join.goodC

theorem jPhi_mem (c : List (Fin (n + 2))) {f : higmanVCCommon_Q (n + 2)} (hf : f ∈ PhiD n) :
    jPhi (n + 2) c f ∈ PhiD n :=
  goodC c f hf

#audit_axioms GroupApproximation.BooneHigman.Join.jPhi_mem

theorem cross_root_zero {i : ℕ} (hi : i ≤ n) : ∀ b : ℕ,
    Prot [fc n i] (fc n (i + 1) :: List.replicate b (fc n 0)) ∈ PhiD n
  | 0 => Prot_root_mem hi
  | b + 1 => by
    have hne : fc n i ≠ fc n (i + 1) := fc_ne (by omega) (by omega) (by omega)
    have e : fc n (i + 1) :: List.replicate (b + 1) (fc n 0) =
        (fc n (i + 1) :: List.replicate b (fc n 0)) ++ [fc n 0] := by
      rw [List.replicate_succ']
      all_goals rfl
    rw [e, Prot_zero (cons_inc hne [] _) (cons_inc hne.symm _ [])]
    exact (PhiD n).mul_mem (cross_root_zero hi b)
      ((PhiD n).inv_mem (jPhi_mem _ (Arot_mem (Nat.zero_le n))))

#audit_axioms GroupApproximation.BooneHigman.Join.cross_root_zero

/-- **The rotations at adjacent leaves across a root letter**: `P(i t^a, (i+1) 0^b)`. -/
theorem cross_root {i : ℕ} (hi : i ≤ n) : ∀ a b : ℕ,
    Prot (fc n i :: List.replicate a (tl n)) (fc n (i + 1) :: List.replicate b (fc n 0)) ∈ PhiD n
  | 0, b => cross_root_zero hi b
  | a + 1, b => by
    obtain ⟨-, -, hc, hd⟩ := Arot_maps (n := n) (j := i) (by omega)
    have h1 : MapsCone (jperm (n + 2) (Arot n i)) ([tl n, fc n i] ++ List.replicate a (tl n))
        (fc n i :: List.replicate (a + 1) (tl n)) := by
      have h := (hc i le_rfl).append (List.replicate a (tl n))
      rw [show n + 1 - i + i = n + 1 by omega] at h
      exact h
    have h2 : MapsCone (jperm (n + 2) (Arot n i))
        ([tl n, fc n (i + 1)] ++ List.replicate b (fc n 0))
        (fc n (i + 1) :: List.replicate b (fc n 0)) :=
      (hd (i + 1) (by omega) (by omega)).append _
    have hne : fc n i ≠ fc n (i + 1) := fc_ne (by omega) (by omega) (by omega)
    have hx : ¬ [tl n, fc n i] ++ List.replicate a (tl n) <+:
        [tl n, fc n (i + 1)] ++ List.replicate b (fc n 0) := dinc_cons [tl n] hne _ _
    have hy : ¬ [tl n, fc n (i + 1)] ++ List.replicate b (fc n 0) <+:
        [tl n, fc n i] ++ List.replicate a (tl n) := dinc_cons [tl n] hne.symm _ _
    rw [← Prot_conj hx hy (Arot n i) h1 h2]
    refine conj_mem (Arot_mem hi) ?_
    have e1 : [tl n, fc n i] ++ List.replicate a (tl n) =
        [tl n] ++ (fc n i :: List.replicate a (tl n)) := rfl
    have e2 : [tl n, fc n (i + 1)] ++ List.replicate b (fc n 0) =
        [tl n] ++ (fc n (i + 1) :: List.replicate b (fc n 0)) := rfl
    rw [e1, e2, ← jPhi_Prot]
    exact jPhi_t_mem (cross_root hi a b)

#audit_axioms GroupApproximation.BooneHigman.Join.cross_root

/-- **The rotations at adjacent leaves**: `P(w i t^a, w (i+1) 0^b)` lies in `PhiD`. -/
theorem cross_mem (w : List (Fin (n + 2))) {i : ℕ} (hi : i ≤ n) (a b : ℕ) :
    Prot (w ++ fc n i :: List.replicate a (tl n))
      (w ++ fc n (i + 1) :: List.replicate b (fc n 0)) ∈ PhiD n := by
  rw [← jPhi_Prot]
  exact jPhi_mem w (cross_root hi a b)

#audit_axioms GroupApproximation.BooneHigman.Join.cross_mem

end GroupApproximation.BooneHigman.Join
