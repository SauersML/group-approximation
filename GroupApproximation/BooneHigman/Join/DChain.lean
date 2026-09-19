import GroupApproximation.BooneHigman.Join.DBase

/-!
# The cycle of the root cones (lane bh-pal-met-join)

The alphabet is `Fin (n + 2)`.  `fc n i` is the letter `i mod (n + 2)`, and `t = fc n (n + 1)` is
the last letter.

* `K0 n = ℓ(0,1) ℓ(1,2) ⋯ ℓ(n, n+1)`, a word in the one-letter words.  It is the cycle
  `[i] ↦ [i + 1]` (`K0_maps`), and `K0 n ^ (n + 2) = 1` (`K0_pow_self`, by antichain
  faithfulness).
* `telescope_full`: for incomparable `x`, `y`, with `K = jPhi x (K0 n)`,
  `∏_{i < n+2} K · ℓ(x t, y i) = ℓ(x, y)`.
  This is the one place the split relator enters the pentagon identities (`DPent`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

theorem dn2 (n : ℕ) : 1 < n + 2 := by omega

#audit_axioms GroupApproximation.BooneHigman.Join.dn2

/-- The letter `i mod (n + 2)`. -/
def fc (n i : ℕ) : Fin (n + 2) := ⟨i % (n + 2), Nat.mod_lt _ (by omega)⟩

#audit_axioms GroupApproximation.BooneHigman.Join.fc

theorem fc_val_of_lt {i : ℕ} (h : i < n + 2) : (fc n i).val = i := Nat.mod_eq_of_lt h

#audit_axioms GroupApproximation.BooneHigman.Join.fc_val_of_lt

theorem fc_ne {i j : ℕ} (hi : i < n + 2) (hj : j < n + 2) (hij : i ≠ j) : fc n i ≠ fc n j := by
  intro h
  apply hij
  have e := congrArg Fin.val h
  rwa [fc_val_of_lt hi, fc_val_of_lt hj] at e

#audit_axioms GroupApproximation.BooneHigman.Join.fc_ne

theorem fc_mod (i : ℕ) : fc n (i % (n + 2)) = fc n i := Fin.ext (Nat.mod_mod _ _)

#audit_axioms GroupApproximation.BooneHigman.Join.fc_mod

theorem fc_mod_succ (i : ℕ) : fc n (i % (n + 2) + 1) = fc n (i + 1) :=
  Fin.ext (Nat.mod_add_mod _ _ _)

#audit_axioms GroupApproximation.BooneHigman.Join.fc_mod_succ

theorem fc_add_self (i : ℕ) : fc n (i + (n + 2)) = fc n i := Fin.ext (Nat.add_mod_right _ _)

#audit_axioms GroupApproximation.BooneHigman.Join.fc_add_self

theorem fc_val (a : Fin (n + 2)) : fc n a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)

#audit_axioms GroupApproximation.BooneHigman.Join.fc_val

theorem sing_inc {X : Type*} {a b : X} (hab : a ≠ b) : ¬ [a] <+: [b] := fun h =>
  hab (List.cons_prefix_cons.mp h).1

#audit_axioms GroupApproximation.BooneHigman.Join.sing_inc

theorem fc_inc {i j : ℕ} (hi : i < n + 2) (hj : j < n + 2) (hij : i ≠ j) :
    ¬ [fc n i] <+: [fc n j] :=
  sing_inc (fc_ne hi hj hij)

#audit_axioms GroupApproximation.BooneHigman.Join.fc_inc

/-- `Rch n m = ℓ(0,1) ℓ(1,2) ⋯ ℓ(m-1, m)` on one-letter words. -/
noncomputable def Rch (n : ℕ) : ℕ → higmanVCCommon_Q (n + 2)
  | 0 => 1
  | m + 1 => Rch n m * jL [fc n m] [fc n (m + 1)]

#audit_axioms GroupApproximation.BooneHigman.Join.Rch

theorem Rch_maps (n : ℕ) : ∀ m : ℕ, m ≤ n + 1 →
    (∀ i, i < m → MapsCone (jperm (n + 2) (Rch n m)) [fc n i] [fc n (i + 1)]) ∧
    MapsCone (jperm (n + 2) (Rch n m)) [fc n m] [fc n 0] ∧
    (∀ j, m < j → j < n + 2 → MapsCone (jperm (n + 2) (Rch n m)) [fc n j] [fc n j])
  | 0, _ => by
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_, fun j _ _ => ?_⟩
    · show MapsCone (jperm (n + 2) 1) _ _
      exact dmc_one _
    · show MapsCone (jperm (n + 2) 1) _ _
      exact dmc_one _
  | m + 1, hm => by
    obtain ⟨h1, h2, h3⟩ := Rch_maps n m (by omega)
    have hl1 : ¬ [fc n m] <+: [fc n (m + 1)] := fc_inc (by omega) (by omega) (by omega)
    have hl2 : ¬ [fc n (m + 1)] <+: [fc n m] := fc_inc (by omega) (by omega) (by omega)
    have hfix : ∀ j, j < n + 2 → j ≠ m → j ≠ m + 1 →
        MapsCone (jperm (n + 2) (jL [fc n m] [fc n (m + 1)])) [fc n j] [fc n j] :=
      fun j hj h1 h2 => dmc_jL_fix hl1 hl2 (fc_inc (by omega) hj (Ne.symm h1))
        (fc_inc hj (by omega) h1) (fc_inc (by omega) hj (Ne.symm h2)) (fc_inc hj (by omega) h2)
    refine ⟨fun i hi => ?_, ?_, fun j hj hj' => ?_⟩
    · show MapsCone (jperm (n + 2) (Rch n m * jL [fc n m] [fc n (m + 1)])) _ _
      rcases Nat.lt_or_ge i m with h | h
      · exact dmc_mul (hfix i (by omega) (by omega) (by omega)) (h1 i h)
      · have hi' : i = m := by omega
        rw [hi']
        exact dmc_mul (dmc_jL_left hl1 hl2) (h3 (m + 1) (by omega) (by omega))
    · show MapsCone (jperm (n + 2) (Rch n m * jL [fc n m] [fc n (m + 1)])) _ _
      exact dmc_mul (dmc_jL_right hl1 hl2) h2
    · show MapsCone (jperm (n + 2) (Rch n m * jL [fc n m] [fc n (m + 1)])) _ _
      exact dmc_mul (hfix j hj' (by omega) (by omega)) (h3 j (by omega) hj')

#audit_axioms GroupApproximation.BooneHigman.Join.Rch_maps

/-- The one-letter words, as a finite set. -/
def rootsF (n : ℕ) : Finset (List (Fin (n + 2))) := Finset.univ.image fun a => [a]

#audit_axioms GroupApproximation.BooneHigman.Join.rootsF

theorem mem_rootsF (a : Fin (n + 2)) : [a] ∈ rootsF n :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

#audit_axioms GroupApproximation.BooneHigman.Join.mem_rootsF

theorem rootsF_isAC : IsAC (rootsF n) := by
  intro u hu v hv huv
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hv
  exact sing_inc fun hab => huv (by rw [hab])

#audit_axioms GroupApproximation.BooneHigman.Join.rootsF_isAC

theorem Rch_mem (n : ℕ) : ∀ m : ℕ, Rch n m ∈ jH (n + 2) (rootsF n)
  | 0 => (jH (n + 2) (rootsF n)).one_mem
  | m + 1 => (jH (n + 2) (rootsF n)).mul_mem (Rch_mem n m) (jL_mem_jH (mem_rootsF _) (mem_rootsF _))

#audit_axioms GroupApproximation.BooneHigman.Join.Rch_mem

/-- The cycle of the one-letter words. -/
noncomputable def K0 (n : ℕ) : higmanVCCommon_Q (n + 2) := Rch n (n + 1)

#audit_axioms GroupApproximation.BooneHigman.Join.K0

theorem K0_maps (i : ℕ) : MapsCone (jperm (n + 2) (K0 n)) [fc n i] [fc n (i + 1)] := by
  have hi := Nat.mod_lt i (show 0 < n + 2 by omega)
  rw [← fc_mod i, ← fc_mod_succ i]
  obtain ⟨h1, h2, -⟩ := Rch_maps n (n + 1) le_rfl
  rcases Nat.lt_or_ge (i % (n + 2)) (n + 1) with h | h
  · exact h1 _ h
  · have e : i % (n + 2) = n + 1 := by omega
    rw [e]
    have e2 : fc n (n + 1 + 1) = fc n 0 :=
      Fin.ext (show (n + 1 + 1) % (n + 2) = 0 % (n + 2) by
        rw [Nat.zero_mod]; exact Nat.mod_self (n + 2))
    rw [e2]
    exact h2

#audit_axioms GroupApproximation.BooneHigman.Join.K0_maps

theorem K0_pow_maps : ∀ (m i : ℕ), MapsCone (jperm (n + 2) (K0 n ^ m)) [fc n i] [fc n (i + m)]
  | 0, i => by
    rw [pow_zero]
    exact dmc_one _
  | m + 1, i => by
    rw [pow_succ, show i + (m + 1) = i + 1 + m by omega]
    exact dmc_mul (K0_maps i) (K0_pow_maps m (i + 1))

#audit_axioms GroupApproximation.BooneHigman.Join.K0_pow_maps

theorem prepend_head {X : Type*} (z : Cantor X) : prepend [z 0] (dropN 1 z) = z := by
  funext k
  cases k with
  | zero => simp [prepend]
  | succ k => simp [prepend, dropN]

#audit_axioms GroupApproximation.BooneHigman.Join.prepend_head

theorem perm_eq_one_of_roots {X : Type*} {f : Equiv.Perm (Cantor X)}
    (h : ∀ a : X, MapsCone f [a] [a]) : f = 1 := by
  refine Equiv.ext fun z => ?_
  have e := h (z 0) (dropN 1 z)
  rw [prepend_head] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Join.perm_eq_one_of_roots

theorem K0_pow_self : K0 n ^ (n + 2) = 1 := by
  refine jH_eq_one_of_jperm (dn2 n) rootsF_isAC
    ((jH (n + 2) (rootsF n)).pow_mem (Rch_mem n (n + 1)) _) ?_
  refine perm_eq_one_of_roots fun a => ?_
  have h := K0_pow_maps (n := n) (n + 2) a.val
  rwa [fc_add_self, fc_val] at h

#audit_axioms GroupApproximation.BooneHigman.Join.K0_pow_self

/-- Products over the alphabet, as products over `0, …, n + 1`. -/
theorem finRange_eq_range_map {α : Type*} (g : Fin (n + 2) → α) :
    (List.finRange (n + 2)).map g = (List.range (n + 2)).map fun i => g (fc n i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_finRange, List.getElem_range]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt (by simpa using h1)).symm

#audit_axioms GroupApproximation.BooneHigman.Join.finRange_eq_range_map

/-- **Telescoping**, partial products. -/
theorem telescope {x y : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) : ∀ m : ℕ,
    ((List.range m).map fun i =>
        jPhi (n + 2) x (K0 n) * jL (x ++ [fc n (n + 1)]) (y ++ [fc n i])).prod =
      ((List.range m).map fun i => jL (x ++ [fc n i]) (y ++ [fc n i])).prod *
        jPhi (n + 2) x (K0 n ^ m)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append, List.prod_append,
      telescope h1 h2 m]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have e : fc n (n + 1 + (m + 1)) = fc n m := by
      rw [show n + 1 + (m + 1) = m + (n + 2) by omega, fc_add_self]
    have hx : MapsCone (jperm (n + 2) (jPhi (n + 2) x (K0 n ^ (m + 1))))
        (x ++ [fc n (n + 1)]) (x ++ [fc n m]) := by
      have h := dmc_phi x (K0_pow_maps (n := n) (m + 1) (n + 1))
      rwa [e] at h
    have hy : MapsCone (jperm (n + 2) (jPhi (n + 2) x (K0 n ^ (m + 1)))) (y ++ [fc n m])
        (y ++ [fc n m]) :=
      dmc_phi_fix x _ (dinc_append_right h1 h2 _) (dinc_append_left h2 h1 _)
    have hc := rcl (dn2 n) (jPhi (n + 2) x (K0 n ^ (m + 1))) (dinc_append h1 h2 _ _)
      (dinc_append h2 h1 _ _) hx hy
    have hK : jPhi (n + 2) x (K0 n ^ (m + 1)) =
        jPhi (n + 2) x (K0 n ^ m) * jPhi (n + 2) x (K0 n) := by
      rw [pow_succ, map_mul]
    rw [← hc, hK]
    group

#audit_axioms GroupApproximation.BooneHigman.Join.telescope

/-- **Telescoping**: `∏_{i < n+2} K · ℓ(x t, y i) = ℓ(x, y)` with `K = jPhi x (K0 n)`. -/
theorem telescope_full {x y : List (Fin (n + 2))} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) :
    ((List.range (n + 2)).map fun i =>
        jPhi (n + 2) x (K0 n) * jL (x ++ [fc n (n + 1)]) (y ++ [fc n i])).prod = jL x y := by
  rw [telescope h1 h2 (n + 2), K0_pow_self, map_one, mul_one, jL_split_prod h1 h2,
    finRange_eq_range_map]

#audit_axioms GroupApproximation.BooneHigman.Join.telescope_full

end GroupApproximation.BooneHigman.Join
