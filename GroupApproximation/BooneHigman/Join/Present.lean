import GroupApproximation.BooneHigman.Join.Closure

/-!
# The all-swaps relators present `V_2` (lane bh-pal-met-join)

`higmanVC_ker_le_two`: `ker (higmanVC_evalAll 2) ≤ normalClosure (higmanVC_rels 2 ⊤)`.  This is
half (1) of the transfer (`EnvelopeHigmanVCAllReduce`), for the binary alphabet, with no
hypotheses.

Proof.  Every element of `Q = higmanVCCommon_Q 2` is a normal form `f · σ`, with `f` in the lift
`Phi` of Thompson's `F` and `σ` in the antichain subgroup of a tree code (`mem_JN`).  Right
multiplication by a letter keeps this form: split the letter deep (`proc`) and apply the
expansion lemma along paths (`path_expand`).  A normal form with trivial boundary action is `1`
(`N_ker`): its `F`-part and its permutation part act by maps that are monotone and rigid
respectively, so both are trivial, and both parts are faithful (`Phi_faithful`, antichain
faithfulness).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

open BTree

theorem mul_mul_eq {G : Type*} [Group G] {s a b f₁ s₁ f₂ s₂ : G} (e₁ : s * a = f₁ * s₁)
    (e₂ : s₁ * b = f₂ * s₂) : s * (a * b) = f₁ * f₂ * s₂ :=
  calc s * (a * b) = (s * a) * b := (mul_assoc s a b).symm
    _ = (f₁ * s₁) * b := by rw [e₁]
    _ = f₁ * (s₁ * b) := mul_assoc f₁ s₁ b
    _ = f₁ * (f₂ * s₂) := by rw [e₂]
    _ = f₁ * f₂ * s₂ := (mul_assoc f₁ f₂ s₂).symm

#audit_axioms GroupApproximation.BooneHigman.Join.mul_mul_eq

theorem mul_eq_of_eq {G : Type*} [Group G] {f σ D f' σ' : G} (e : σ * D = f' * σ') :
    f * σ * D = f * f' * σ' :=
  calc f * σ * D = f * (σ * D) := mul_assoc f σ D
    _ = f * (f' * σ') := by rw [e]
    _ = f * f' * σ' := (mul_assoc f f' σ').symm

#audit_axioms GroupApproximation.BooneHigman.Join.mul_eq_of_eq

/-- **Right multiplication by a deep split keeps the normal form.** -/
theorem proc : ∀ (K : ℕ) (x y : List (Fin 2)), ¬ x <+: y → ¬ y <+: x → ∀ (T : BTree),
    ∀ σ ∈ jH 2 T.lset, (∀ w : List (Fin 2), w.length = K →
      T.AtOrBelow (x ++ w) ∧ T.AtOrBelow (y ++ w)) →
    ∃ T' : BTree, ∃ f ∈ Phi, ∃ σ' ∈ jH 2 T'.lset,
      σ * higmanVCCommon_mk 2 (higmanVCCommon_deep 2 K x y) = f * σ' ∧
      ∀ z, AvoidsPieces K x y z → T.AtOrBelow z → T'.AtOrBelow z
  | 0, x, y, hxy, hyx, T, σ, hσ, hK => by
    obtain ⟨hx, hy⟩ := hK [] rfl
    rw [List.append_nil] at hx hy
    obtain ⟨c, hc, s, rfl⟩ := hx
    obtain ⟨T₁, f₁, hf₁, σ₁, hσ₁, e₁, hmem₁, hsurv₁, hpres₁⟩ := path_expand s T c hc σ hσ
    obtain ⟨c', hc', s', rfl⟩ := hpres₁ _ hyx hy
    obtain ⟨T₂, f₂, hf₂, σ₂, hσ₂, e₂, hmem₂, hsurv₂, hpres₂⟩ := path_expand s' T₁ c' hc' σ₁ hσ₁
    have hx₂ : c ++ s ∈ T₂.leaves := hsurv₂ _ hmem₁ hxy
    refine ⟨T₂, f₁ * f₂, Phi.mul_mem hf₁ hf₂, σ₂ * jL (c ++ s) (c' ++ s'),
      (jH 2 _).mul_mem hσ₂ (jL_mem_jH (mem_lset.mpr hx₂) (mem_lset.mpr hmem₂)), ?_, ?_⟩
    · show σ * jL (c ++ s) (c' ++ s') = _
      rw [e₁, e₂]
      group
    · intro z hz hzT
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz [] rfl
      rw [List.append_nil] at h1 h2 h3 h4
      exact hpres₂ z h3 (hpres₁ z h1 hzT)
  | K + 1, x, y, hxy, hyx, T, σ, hσ, hK => by
    have hK0 : ∀ w : List (Fin 2), w.length = K →
        T.AtOrBelow ((x ++ [0]) ++ w) ∧ T.AtOrBelow ((y ++ [0]) ++ w) := by
      intro w hw
      have h := hK (0 :: w) (by simp [hw])
      simpa [List.append_assoc] using h
    obtain ⟨T₁, f₁, hf₁, σ₁, hσ₁, e₁, hp₁⟩ :=
      proc K (x ++ [0]) (y ++ [0]) (incomp_append hxy hyx _ _) (incomp_append hyx hxy _ _)
        T σ hσ hK0
    have hK1 : ∀ w : List (Fin 2), w.length = K →
        T₁.AtOrBelow ((x ++ [1]) ++ w) ∧ T₁.AtOrBelow ((y ++ [1]) ++ w) := by
      intro w hw
      have h := hK (1 :: w) (by simp [hw])
      rw [List.append_assoc, List.append_assoc]
      refine ⟨hp₁ _ ?_ h.1, hp₁ _ ?_ h.2⟩
      · intro w' hw'
        rw [List.append_assoc, List.append_assoc]
        exact ⟨⟨incomp_diff (by decide) _ _, incomp_diff (by decide) _ _⟩,
          ⟨incomp_append hxy hyx _ _, incomp_append hyx hxy _ _⟩⟩
      · intro w' hw'
        rw [List.append_assoc, List.append_assoc]
        exact ⟨⟨incomp_append hyx hxy _ _, incomp_append hxy hyx _ _⟩,
          ⟨incomp_diff (by decide) _ _, incomp_diff (by decide) _ _⟩⟩
    obtain ⟨T₂, f₂, hf₂, σ₂, hσ₂, e₂, hp₂⟩ :=
      proc K (x ++ [1]) (y ++ [1]) (incomp_append hxy hyx _ _) (incomp_append hyx hxy _ _)
        T₁ σ₁ hσ₁ hK1
    refine ⟨T₂, f₁ * f₂, Phi.mul_mem hf₁ hf₂, σ₂, hσ₂, ?_, ?_⟩
    · rw [deep_succ_two]
      exact mul_mul_eq e₁ e₂
    · intro z hz hzT
      exact hp₂ z (avoidsPieces_succ hz 1) (hp₁ z (avoidsPieces_succ hz 0) hzT)

#audit_axioms GroupApproximation.BooneHigman.Join.proc

/-- The normal forms. -/
def JN : Set (higmanVCCommon_Q 2) :=
  {q | ∃ f ∈ Phi, ∃ T : BTree, ∃ σ ∈ jH 2 T.lset, q = f * σ}

#audit_axioms GroupApproximation.BooneHigman.Join.JN

theorem one_mem_JN : (1 : higmanVCCommon_Q 2) ∈ JN :=
  ⟨1, Phi.one_mem, BTree.leaf, 1, Subgroup.one_mem _, (one_mul 1).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Join.one_mem_JN

/-- Right multiplication by a letter keeps the normal form. -/
theorem mul_jL_mem_JN {q : higmanVCCommon_Q 2} (hq : q ∈ JN) (x y : List (Fin 2)) :
    q * jL x y ∈ JN := by
  by_cases h : ¬ x <+: y ∧ ¬ y <+: x
  · obtain ⟨f, hf, T, σ, hσ, rfl⟩ := hq
    have hK : ∀ w : List (Fin 2), w.length = T.depth →
        T.AtOrBelow (x ++ w) ∧ T.AtOrBelow (y ++ w) := fun w hw =>
      ⟨atOrBelow_of_depth_le T (by simp [hw]), atOrBelow_of_depth_le T (by simp [hw])⟩
    obtain ⟨T', f', hf', σ', hσ', e, -⟩ := proc T.depth x y h.1 h.2 T σ hσ hK
    refine ⟨f * f', Phi.mul_mem hf hf', T', σ', hσ', ?_⟩
    have hd : jL x y = higmanVCCommon_mk 2 (higmanVCCommon_deep 2 T.depth x y) :=
      (higmanVCCommon_mk_deep T.depth h.1 h.2).symm
    rw [hd]
    exact mul_eq_of_eq e
  · rw [jL_comparable h, mul_one]
    exact hq

#audit_axioms GroupApproximation.BooneHigman.Join.mul_jL_mem_JN

theorem mul_mk_mem_JN (g : FreeGroup (List (Fin 2) × List (Fin 2))) :
    ∀ q ∈ JN, q * higmanVCCommon_mk 2 g ∈ JN := by
  induction g using FreeGroup.induction_on with
  | C1 =>
    intro q hq
    rwa [map_one, mul_one]
  | of p =>
    intro q hq
    exact mul_jL_mem_JN hq p.1 p.2
  | inv_of p _ =>
    intro q hq
    rw [map_inv, show (higmanVCCommon_mk 2 (FreeGroup.of p))⁻¹ = jL p.1 p.2 from jL_inv p.1 p.2]
    exact mul_jL_mem_JN hq p.1 p.2
  | mul a b iha ihb =>
    intro q hq
    rw [map_mul, ← mul_assoc]
    exact ihb _ (iha q hq)

#audit_axioms GroupApproximation.BooneHigman.Join.mul_mk_mem_JN

/-- **Every element of the all-swaps quotient of `V_2` is a normal form.** -/
theorem mem_JN (q : higmanVCCommon_Q 2) : q ∈ JN := by
  obtain ⟨g, rfl⟩ := mk_surj q
  have h := mul_mk_mem_JN g 1 one_mem_JN
  rwa [one_mul] at h

#audit_axioms GroupApproximation.BooneHigman.Join.mem_JN

/-- **The evaluation of the all-swaps quotient of `V_2` is injective.** -/
theorem eq_one_of_jperm_eq_one {q : higmanVCCommon_Q 2} (h : jperm 2 q = 1) : q = 1 := by
  obtain ⟨f, hf, T, σ, hσ, rfl⟩ := mem_JN q
  exact N_ker (lset_isAC T) hf hσ h

#audit_axioms GroupApproximation.BooneHigman.Join.eq_one_of_jperm_eq_one

/-- **The all-swaps relators present `V_2`.** -/
theorem higmanVC_ker_le_two :
    (higmanVC_evalAll 2).ker ≤ Subgroup.normalClosure (higmanVC_rels 2 fun _ => True) := by
  intro r hr
  refine higmanVCCommon_mk_eq_one_iff.mp (eq_one_of_jperm_eq_one ?_)
  show ((higmanVC_evalAll 2 r : ↥(higmanThompsonV (Fin 2))) : Equiv.Perm (Cantor (Fin 2))) = 1
  exact (congrArg Subtype.val (MonoidHom.mem_ker.mp hr)).trans (Subgroup.coe_one _)

#audit_axioms GroupApproximation.BooneHigman.Join.higmanVC_ker_le_two

end GroupApproximation.BooneHigman.Join
