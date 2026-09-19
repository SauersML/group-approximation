import GroupApproximation.BooneHigman.Join.DPent

/-!
# The ray model of `F_{n+2}` (lane bh-pal-met-join)

Cut the boundary minus the point `t t t ⋯` into the cells `t^q j` (`j ≤ n`), and number the
cell `t^q j` by `q (n+1) + j`.  `up n (N, w)` is the stream of cell `N` with tail `w`; it is
injective (`up_injective`).

On `ℕ × Cantor`, Brown's generator `x_N` is `rayR n N`.  It fixes the cells below `N`, sends
cell `N + i` (`i ≤ n + 1`) into cell `N` by prefixing the letter `i`, and moves the cells above
down by `n + 1`.  The shift `x_N ↦ x_{N+1}` is `shHom`, the conjugation by the translation
`(N, w) ↦ (N + 1, w)` (`shHom_rayR`), and it is injective.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- `R_N`, forwards. -/
def rayF (n N : ℕ) (p : ℕ × Cantor (Fin (n + 2))) : ℕ × Cantor (Fin (n + 2)) :=
  if p.1 < N then p
  else if p.1 ≤ N + n + 1 then (N, prepend [fc n (p.1 - N)] p.2)
  else (p.1 - (n + 1), p.2)

#audit_axioms GroupApproximation.BooneHigman.Join.rayF

/-- `R_N`, backwards. -/
def rayG (n N : ℕ) (p : ℕ × Cantor (Fin (n + 2))) : ℕ × Cantor (Fin (n + 2)) :=
  if p.1 < N then p
  else if p.1 = N then (N + (p.2 0).val, dropN 1 p.2)
  else (p.1 + (n + 1), p.2)

#audit_axioms GroupApproximation.BooneHigman.Join.rayG

theorem prepend_single_zero {X : Type*} (a : X) (w : Cantor X) : prepend [a] w 0 = a := by
  simp [prepend]

#audit_axioms GroupApproximation.BooneHigman.Join.prepend_single_zero

theorem dropN_prepend_single {X : Type*} (a : X) (w : Cantor X) : dropN 1 (prepend [a] w) = w :=
  dropN_prepend [a] w

#audit_axioms GroupApproximation.BooneHigman.Join.dropN_prepend_single

theorem rayF_lt {N M : ℕ} (w : Cantor (Fin (n + 2))) (h : M < N) : rayF n N (M, w) = (M, w) := by
  simp [rayF, h]

#audit_axioms GroupApproximation.BooneHigman.Join.rayF_lt

theorem rayF_mid {N M : ℕ} (w : Cantor (Fin (n + 2))) (h1 : N ≤ M) (h2 : M ≤ N + n + 1) :
    rayF n N (M, w) = (N, prepend [fc n (M - N)] w) := by
  simp [rayF, show ¬ M < N by omega, h2]

#audit_axioms GroupApproximation.BooneHigman.Join.rayF_mid

theorem rayF_gt {N M : ℕ} (w : Cantor (Fin (n + 2))) (h : N + n + 1 < M) :
    rayF n N (M, w) = (M - (n + 1), w) := by
  simp [rayF, show ¬ M < N by omega, show ¬ M ≤ N + n + 1 by omega]

#audit_axioms GroupApproximation.BooneHigman.Join.rayF_gt

theorem rayG_lt {N M : ℕ} (w : Cantor (Fin (n + 2))) (h : M < N) : rayG n N (M, w) = (M, w) := by
  simp [rayG, h]

#audit_axioms GroupApproximation.BooneHigman.Join.rayG_lt

theorem rayG_eq (N : ℕ) (w : Cantor (Fin (n + 2))) :
    rayG n N (N, w) = (N + (w 0).val, dropN 1 w) := by
  simp [rayG]

#audit_axioms GroupApproximation.BooneHigman.Join.rayG_eq

theorem rayG_gt {N M : ℕ} (w : Cantor (Fin (n + 2))) (h : N < M) :
    rayG n N (M, w) = (M + (n + 1), w) := by
  simp [rayG, show ¬ M < N by omega, show M ≠ N by omega]

#audit_axioms GroupApproximation.BooneHigman.Join.rayG_gt

theorem rayG_rayF (N : ℕ) (p : ℕ × Cantor (Fin (n + 2))) : rayG n N (rayF n N p) = p := by
  obtain ⟨M, w⟩ := p
  rcases Nat.lt_or_ge M N with h1 | h1
  · rw [rayF_lt w h1, rayG_lt w h1]
  rcases Nat.lt_or_ge (N + n + 1) M with h2 | h2
  · rw [rayF_gt w h2, rayG_gt w (by omega)]
    congr 1
    omega
  · rw [rayF_mid w h1 h2, rayG_eq, prepend_single_zero, dropN_prepend_single,
      fc_val_of_lt (n := n) (i := M - N) (by omega)]
    congr 1
    omega

#audit_axioms GroupApproximation.BooneHigman.Join.rayG_rayF

theorem rayF_rayG (N : ℕ) (p : ℕ × Cantor (Fin (n + 2))) : rayF n N (rayG n N p) = p := by
  obtain ⟨M, w⟩ := p
  rcases Nat.lt_or_ge M N with h1 | h1
  · rw [rayG_lt w h1, rayF_lt w h1]
  rcases Nat.lt_or_ge N M with h2 | h2
  · rw [rayG_gt w h2, rayF_gt w (by omega)]
    congr 1
    omega
  · have hM : M = N := by omega
    rw [hM, rayG_eq]
    have hv := (w 0).isLt
    rw [rayF_mid _ (by omega) (by omega), show N + (w 0).val - N = (w 0).val by omega, fc_val,
      prepend_head]

#audit_axioms GroupApproximation.BooneHigman.Join.rayF_rayG

/-- Brown's generator `x_N` on the ray. -/
def rayR (n N : ℕ) : Equiv.Perm (ℕ × Cantor (Fin (n + 2))) :=
  ⟨rayF n N, rayG n N, rayG_rayF N, rayF_rayG N⟩

#audit_axioms GroupApproximation.BooneHigman.Join.rayR

theorem rayR_apply (N : ℕ) (p : ℕ × Cantor (Fin (n + 2))) : rayR n N p = rayF n N p := rfl

#audit_axioms GroupApproximation.BooneHigman.Join.rayR_apply

/-- The stream of cell `N` with tail `w`. -/
def up (n : ℕ) (p : ℕ × Cantor (Fin (n + 2))) : Cantor (Fin (n + 2)) :=
  prepend (List.replicate (p.1 / (n + 1)) (tl n) ++ [fc n (p.1 % (n + 1))]) p.2

#audit_axioms GroupApproximation.BooneHigman.Join.up

theorem rep_inc {X : Type*} {t a b : X} (ha : a ≠ t) (hb : b ≠ t) :
    ∀ q q' : ℕ, (q ≠ q' ∨ a ≠ b) →
      ¬ List.replicate q t ++ [a] <+: List.replicate q' t ++ [b]
  | 0, 0, h => fun h' => by
    rcases h with h | h
    · exact h rfl
    · exact h (List.cons_prefix_cons.mp h').1
  | 0, q' + 1, _ => fun h' => ha (List.cons_prefix_cons.mp h').1
  | q + 1, 0, _ => fun h' => hb (List.cons_prefix_cons.mp h').1.symm
  | q + 1, q' + 1, h => fun h' => by
    refine rep_inc ha hb q q' ?_ (List.cons_prefix_cons.mp h').2
    rcases h with h | h
    · exact Or.inl fun e => h (by rw [e])
    · exact Or.inr h

#audit_axioms GroupApproximation.BooneHigman.Join.rep_inc

theorem fc_mod_ne_tl (N : ℕ) : fc n (N % (n + 1)) ≠ tl n :=
  fc_ne (by have := Nat.mod_lt N (show 0 < n + 1 by omega); omega) (by omega)
    (by have := Nat.mod_lt N (show 0 < n + 1 by omega); omega)

#audit_axioms GroupApproximation.BooneHigman.Join.fc_mod_ne_tl

theorem up_injective : Function.Injective (up n) := by
  rintro ⟨N, w⟩ ⟨N', w'⟩ h
  simp only [up] at h
  have hu : List.replicate (N / (n + 1)) (tl n) ++ [fc n (N % (n + 1))] =
      List.replicate (N' / (n + 1)) (tl n) ++ [fc n (N' % (n + 1))] := by
    by_contra hne
    have hq : N / (n + 1) ≠ N' / (n + 1) ∨ fc n (N % (n + 1)) ≠ fc n (N' % (n + 1)) := by
      by_contra hc
      push_neg at hc
      exact hne (by rw [hc.1, hc.2])
    have hq' : N' / (n + 1) ≠ N / (n + 1) ∨ fc n (N' % (n + 1)) ≠ fc n (N % (n + 1)) := by
      rcases hq with hq | hq
      · exact Or.inl (Ne.symm hq)
      · exact Or.inr (Ne.symm hq)
    have h1 := rep_inc (fc_mod_ne_tl N) (fc_mod_ne_tl N') _ _ hq
    have h2 := rep_inc (fc_mod_ne_tl N') (fc_mod_ne_tl N) _ _ hq'
    exact Set.disjoint_left.mp (disjoint_cone h1 h2) (prepend_mem_cone _ w)
      (by rw [h]; exact prepend_mem_cone _ w')
  have hlen := congrArg List.length hu
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen
  have hq : N / (n + 1) = N' / (n + 1) := by omega
  obtain ⟨-, hj⟩ := List.append_inj hu (by simp [hq])
  have hj' : fc n (N % (n + 1)) = fc n (N' % (n + 1)) := List.head_eq_of_cons_eq hj
  have hv := congrArg Fin.val hj'
  rw [fc_val_of_lt (n := n) (i := N % (n + 1)) (by have := Nat.mod_lt N (show 0 < n + 1 by omega); omega),
    fc_val_of_lt (n := n) (i := N' % (n + 1))
      (by have := Nat.mod_lt N' (show 0 < n + 1 by omega); omega)] at hv
  have hN : N = N' := by
    rw [← Nat.div_add_mod N (n + 1), ← Nat.div_add_mod N' (n + 1), hq, hv]
  subst hN
  rw [prepend_injective _ h]

#audit_axioms GroupApproximation.BooneHigman.Join.up_injective

/-- The shift of a permutation of the ray: identity on cell `0`, conjugate one cell up. -/
def shF {X : Type*} (g : Equiv.Perm (ℕ × Cantor X)) : ℕ × Cantor X → ℕ × Cantor X
  | (0, w) => (0, w)
  | (N + 1, w) => ((g (N, w)).1 + 1, (g (N, w)).2)

#audit_axioms GroupApproximation.BooneHigman.Join.shF

theorem shF_inv {X : Type*} (g : Equiv.Perm (ℕ × Cantor X)) (p : ℕ × Cantor X) :
    shF g⁻¹ (shF g p) = p := by
  obtain ⟨N, w⟩ := p
  cases N with
  | zero => rfl
  | succ N =>
    show ((g⁻¹ ((g (N, w)).1, (g (N, w)).2)).1 + 1, (g⁻¹ ((g (N, w)).1, (g (N, w)).2)).2) = _
    rw [Prod.mk.eta, Equiv.Perm.inv_apply_self]
    all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.shF_inv

/-- The shift, as a permutation. -/
def shP {X : Type*} (g : Equiv.Perm (ℕ × Cantor X)) : Equiv.Perm (ℕ × Cantor X) :=
  ⟨shF g, shF g⁻¹, shF_inv g, fun p => by
    have h := shF_inv g⁻¹ p
    rwa [inv_inv] at h⟩

#audit_axioms GroupApproximation.BooneHigman.Join.shP

theorem shP_mul {X : Type*} (g h : Equiv.Perm (ℕ × Cantor X)) : shP (g * h) = shP g * shP h := by
  ext ⟨N, w⟩ : 1
  cases N with
  | zero => rfl
  | succ N =>
    show ((g (h (N, w))).1 + 1, (g (h (N, w))).2) =
      ((g ((h (N, w)).1, (h (N, w)).2)).1 + 1, (g ((h (N, w)).1, (h (N, w)).2)).2)
    rw [Prod.mk.eta]

#audit_axioms GroupApproximation.BooneHigman.Join.shP_mul

/-- The shift homomorphism. -/
def shHom (X : Type*) : Equiv.Perm (ℕ × Cantor X) →* Equiv.Perm (ℕ × Cantor X) where
  toFun := shP
  map_one' := by
    ext ⟨N, w⟩ : 1
    cases N <;> rfl
  map_mul' := shP_mul

#audit_axioms GroupApproximation.BooneHigman.Join.shHom

theorem shHom_injective (X : Type*) : Function.Injective (shHom X) := by
  intro g h e
  ext ⟨N, w⟩ : 1
  have e1 := congrArg (fun f : Equiv.Perm (ℕ × Cantor X) => f (N + 1, w)) e
  simp only at e1
  change ((g (N, w)).1 + 1, (g (N, w)).2) = ((h (N, w)).1 + 1, (h (N, w)).2) at e1
  rw [Prod.mk.injEq] at e1
  exact Prod.ext (by have := e1.1; omega) e1.2

#audit_axioms GroupApproximation.BooneHigman.Join.shHom_injective

theorem shHom_rayR (N : ℕ) : shHom (Fin (n + 2)) (rayR n N) = rayR n (N + 1) := by
  ext ⟨M, w⟩ : 1
  cases M with
  | zero =>
    show ((0 : ℕ), w) = rayF n (N + 1) (0, w)
    rw [rayF_lt w (by omega)]
  | succ M =>
    show ((rayF n N (M, w)).1 + 1, (rayF n N (M, w)).2) = rayF n (N + 1) (M + 1, w)
    rcases Nat.lt_or_ge M N with h1 | h1
    · rw [rayF_lt w h1, rayF_lt w (by omega)]
    rcases Nat.lt_or_ge (N + n + 1) M with h2 | h2
    · rw [rayF_gt w h2, rayF_gt w (by omega), show M - (n + 1) + 1 = M + 1 - (n + 1) by omega]
    · rw [rayF_mid w h1 h2, rayF_mid w (by omega) (by omega),
        show M + 1 - (N + 1) = M - N by omega]

#audit_axioms GroupApproximation.BooneHigman.Join.shHom_rayR

end GroupApproximation.BooneHigman.Join
