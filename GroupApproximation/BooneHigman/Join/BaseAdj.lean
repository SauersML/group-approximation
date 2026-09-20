import GroupApproximation.BooneHigman.Join.Base

/-!
# Base identities for every adjacent pair across the root (lane bh-pal-met-join)

* `baseR_phi`: `BaseR p q → BaseR (w p) (w q)`.
* `baseR_transport`: conjugation by `g ∈ Phi` carrying `p̂ ↦ p`, `q̂ ↦ q` preserves `BaseR`.
* `baseR_adj a b : BaseR (0 1^a) (1 0^b)`.  The four cases start from `BaseR 0 1`, prefixed by
  `ε`, `0`, `1` or `10`, and are transported by products of prefixed powers of `X0`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

theorem baseR_phi (w : List (Fin 2)) {p q : List (Fin 2)} (h : BaseR p q) :
    BaseR (w ++ p) (w ++ q) := by
  obtain ⟨f, hf, ρ, hρ, e, m1, m2, m3, hfix⟩ := h
  refine ⟨jPhi 2 w f, jPhi_mem_Phi w hf, jPhi 2 w ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine jH_mono ?_ (jPhi_mem_jH w hρ)
    intro c hc
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
    obtain ⟨c', hc', rfl⟩ := hc
    rcases hc' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (List.append_assoc _ _ _).symm)
    · exact Or.inr (Or.inr (List.append_assoc _ _ _).symm)
  · rw [← map_mul, ← e, jPhi_jL]
  · have h' := mc_phi w m1
    rwa [← List.append_assoc] at h'
  · have h' := mc_phi w m2
    rwa [← List.append_assoc, ← List.append_assoc] at h'
  · have h' := mc_phi w m3
    rwa [← List.append_assoc] at h'
  · intro z hz1 hz2
    rw [jperm_jPhi]
    by_cases hz : IsStreamPrefix w z
    · obtain ⟨z', rfl⟩ := mem_cone_iff.mp (mem_cone.mpr hz)
      have n : ∀ c : List (Fin 2), ¬ IsStreamPrefix (w ++ c) (prepend w z') →
          ¬ IsStreamPrefix c z' := by
        intro c hc h
        obtain ⟨y, rfl⟩ := mem_cone_iff.mp (mem_cone.mpr h)
        apply hc
        rw [← prepend_append]
        exact isStreamPrefix_prepend _ y
      rw [localize_apply_prepend, hfix z' (n p hz1) (n q hz2)]
    · exact localize_apply_of_not hz _

#audit_axioms GroupApproximation.BooneHigman.Join.baseR_phi

theorem baseR_transport {p q p' q' : List (Fin 2)} (h1 : ¬ p <+: q) (h2 : ¬ q <+: p)
    {g : higmanVCCommon_Q 2} (hg : g ∈ Phi) (hp : MapsCone (jperm 2 g) p p')
    (hq : MapsCone (jperm 2 g) q q') (h : BaseR p q) : BaseR p' q' := by
  obtain ⟨f, hf, ρ, hρ, e, m1, m2, m3, hfix⟩ := h
  have hC : IsAC {p, q ++ [0], q ++ [1]} :=
    isAC_three (by simpa using incomp_append h1 h2 [] [0]) (by simpa using incomp_append h2 h1 [0] [])
      (by simpa using incomp_append h1 h2 [] [1]) (by simpa using incomp_append h2 h1 [1] [])
      incomp_child incomp_child'
  refine ⟨g * f * g⁻¹, Phi.mul_mem (Phi.mul_mem hg hf) (Phi.inv_mem hg), g * ρ * g⁻¹, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · refine rcl_H jd2 hC g ?_ hρ
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨p', by simp, hp⟩
    · exact ⟨q' ++ [0], by simp, hq.append [0]⟩
    · exact ⟨q' ++ [1], by simp, hq.append [1]⟩
  · rw [← rcl jd2 g h1 h2 hp hq, e]
    group
  · exact mc_mul (mc_inv hp) (mc_mul m1 (hp.append [0]))
  · exact mc_mul (mc_inv (hq.append [0])) (mc_mul m2 (hp.append [1]))
  · exact mc_mul (mc_inv (hq.append [1])) (mc_mul m3 hq)
  · intro z hz1 hz2
    have hn : ∀ {c c' : List (Fin 2)}, MapsCone (jperm 2 g) c c' → ¬ IsStreamPrefix c' z →
        ¬ IsStreamPrefix c ((jperm 2 g)⁻¹ z) := by
      intro c c' hm hz' hc
      obtain ⟨y, hy⟩ := mem_cone_iff.mp (mem_cone.mpr hc)
      apply hz'
      have ez : z = prepend c' y := by
        rw [← hm y, ← hy, perm_apply_inv_self]
      rw [ez]
      exact isStreamPrefix_prepend c' y
    have hz := hfix _ (hn hp hz1) (hn hq hz2)
    rw [jperm_mul, jperm_mul, jperm_inv]
    simp only [Equiv.Perm.mul_apply]
    rw [hz, perm_apply_inv_self]

#audit_axioms GroupApproximation.BooneHigman.Join.baseR_transport

theorem mc_X0_pow (k : ℕ) : MapsCone (jperm 2 (X0 ^ k)) [0] (List.replicate (k + 1) 0) := by
  induction k with
  | zero =>
    rw [pow_zero, jperm_one]
    exact mapsCone_one _
  | succ k ih =>
    rw [pow_succ]
    have h := mc_mul mapsCone_X0_zero (ih.append [0])
    rwa [← List.replicate_succ'] at h

#audit_axioms GroupApproximation.BooneHigman.Join.mc_X0_pow

theorem mc_X0inv_pow (k : ℕ) : MapsCone (jperm 2 (X0⁻¹ ^ k)) [1] (List.replicate (k + 1) 1) := by
  induction k with
  | zero =>
    rw [pow_zero, jperm_one]
    exact mapsCone_one _
  | succ k ih =>
    rw [pow_succ]
    have h := mc_mul (mc_inv mapsCone_X0_one_one) (ih.append [1])
    rwa [← List.replicate_succ'] at h

#audit_axioms GroupApproximation.BooneHigman.Join.mc_X0inv_pow

theorem nprefix_zero_one (l l' : List (Fin 2)) : ¬ (0 :: l) <+: (1 :: l') := fun h =>
  absurd (List.cons_prefix_cons.mp h).1 (by decide)

#audit_axioms GroupApproximation.BooneHigman.Join.nprefix_zero_one

theorem nprefix_one_zero (l l' : List (Fin 2)) : ¬ (1 :: l) <+: (0 :: l') := fun h =>
  absurd (List.cons_prefix_cons.mp h).1 (by decide)

#audit_axioms GroupApproximation.BooneHigman.Join.nprefix_one_zero

theorem pow_mem_Phi {q : higmanVCCommon_Q 2} (hq : q ∈ Phi) (k : ℕ) : q ^ k ∈ Phi :=
  Phi.pow_mem hq k

#audit_axioms GroupApproximation.BooneHigman.Join.pow_mem_Phi

/-- **The base identities for the adjacent pairs across the root.** -/
theorem baseR_adj (a b : ℕ) :
    BaseR (0 :: List.replicate a 1) (1 :: List.replicate b 0) := by
  have h01 : ¬ ([0] : List (Fin 2)) <+: [1] := by decide
  have h10 : ¬ ([1] : List (Fin 2)) <+: [0] := by decide
  cases a with
  | zero =>
    cases b with
    | zero => exact baseR_zero_one
    | succ m =>
      refine baseR_transport (p := [0, 0]) (q := [0, 1]) (by decide) (by decide)
        (Phi.mul_mem (jPhi_mem_Phi [1] (pow_mem_Phi X0_mem_Phi m)) (Phi.inv_mem X0_mem_Phi))
        ?_ ?_ (baseR_phi [0] baseR_zero_one)
      · exact mc_mul (mc_inv mapsCone_X0_zero) (mc_phi_fix [1] _ (by decide) (by decide))
      · exact mc_mul (mc_inv mapsCone_X0_one_zero) (mc_phi [1] (mc_X0_pow m))
  | succ k =>
    cases b with
    | zero =>
      refine baseR_transport (p := [1, 0]) (q := [1, 1]) (by decide) (by decide)
        (Phi.mul_mem (jPhi_mem_Phi [0] (pow_mem_Phi (Phi.inv_mem X0_mem_Phi) k)) X0_mem_Phi)
        ?_ ?_ (baseR_phi [1] baseR_zero_one)
      · exact mc_mul mapsCone_X0_one_zero (mc_phi [0] (mc_X0inv_pow k))
      · exact mc_mul mapsCone_X0_one_one (mc_phi_fix [0] _ (by decide) (by decide))
    | succ m =>
      have hY : MapsCone (jperm 2 (Y 1)) [1, 0] [1, 0, 0] := mc_phi [1] mapsCone_X0_zero
      have hY' : MapsCone (jperm 2 (Y 1)) [1, 1, 0] [1, 0, 1] := mc_phi [1] mapsCone_X0_one_zero
      refine baseR_transport (p := [1, 0, 0]) (q := [1, 0, 1]) (by decide) (by decide)
        (Phi.mul_mem (Phi.mul_mem (Phi.mul_mem
          (jPhi_mem_Phi [0] (pow_mem_Phi (Phi.inv_mem X0_mem_Phi) k))
          (jPhi_mem_Phi [1] (pow_mem_Phi X0_mem_Phi m))) X0_mem_Phi)
          (Phi.inv_mem (Y_mem_Phi 1)))
        ?_ ?_ (baseR_phi [1, 0] baseR_zero_one)
      · exact mc_mul (mc_inv hY) (mc_mul mapsCone_X0_one_zero
          (mc_mul (mc_phi_fix [1] _ (by decide) (by decide)) (mc_phi [0] (mc_X0inv_pow k))))
      · exact mc_mul (mc_inv hY') (mc_mul (mapsCone_X0_one_one.append [0])
          (mc_mul (mc_phi [1] (mc_X0_pow m))
            (mc_phi_fix [0] _ (nprefix_zero_one _ _) (nprefix_one_zero _ _))))

#audit_axioms GroupApproximation.BooneHigman.Join.baseR_adj

end GroupApproximation.BooneHigman.Join
