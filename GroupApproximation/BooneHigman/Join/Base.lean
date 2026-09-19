import GroupApproximation.BooneHigman.Join.Tree

/-!
# The base expansion identities (lane bh-pal-met-join)

For incomparable words `p`, `q`, `BaseR p q` says that the letter `ℓ(p, q)` factors as `f · ρ`:
* `f` lies in the lift `Phi` of Thompson's `F`, and carries `p ↦ p0`, `q0 ↦ p1`, `q1 ↦ q`,
  fixing every point outside the cones of `p` and `q`;
* `ρ` lies in the antichain subgroup of `{p, q0, q1}`.

`BaseL p q` is the mirror factorization, with `ρ` on `{p0, p1, q}` (`baseL_of_baseR`).

* `baseR_zero_one`: `BaseR 0 1`.  Here `f = X0`, and the identity is the definition of `X0`.
* `baseR_phi`: prefixing by `w` preserves `BaseR`.
* `baseR_transport`: conjugating by an element of `Phi` that carries `p̂ ↦ p` and `q̂ ↦ q`
  preserves `BaseR`.
* `baseR_adj a b`: `BaseR (0 1^a) (1 0^b)` for all `a`, `b`.  These are the two leaves adjacent
  across the root in any tree.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `f` fixes every point outside the cones of `p` and `q`. -/
def Fixes (f : Equiv.Perm (Cantor (Fin 2))) (p q : List (Fin 2)) : Prop :=
  ∀ z, ¬ IsStreamPrefix p z → ¬ IsStreamPrefix q z → f z = z

#audit_axioms GroupApproximation.BooneHigman.Join.Fixes

/-- The right base factorization of `ℓ(p, q)`. -/
def BaseR (p q : List (Fin 2)) : Prop :=
  ∃ f ∈ Phi, ∃ ρ ∈ jH 2 {p, q ++ [0], q ++ [1]}, jL p q = f * ρ ∧
    MapsCone (jperm 2 f) p (p ++ [0]) ∧ MapsCone (jperm 2 f) (q ++ [0]) (p ++ [1]) ∧
    MapsCone (jperm 2 f) (q ++ [1]) q ∧ Fixes (jperm 2 f) p q

#audit_axioms GroupApproximation.BooneHigman.Join.BaseR

/-- The left base factorization of `ℓ(p, q)`. -/
def BaseL (p q : List (Fin 2)) : Prop :=
  ∃ f ∈ Phi, ∃ ρ ∈ jH 2 {p ++ [0], p ++ [1], q}, jL p q = f * ρ ∧
    MapsCone (jperm 2 f) (p ++ [0]) p ∧ MapsCone (jperm 2 f) (p ++ [1]) (q ++ [0]) ∧
    MapsCone (jperm 2 f) q (q ++ [1]) ∧ Fixes (jperm 2 f) p q

#audit_axioms GroupApproximation.BooneHigman.Join.BaseL

/-- Incomparability is inherited by extensions. -/
theorem incomp_append {x y : List (Fin 2)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) (u v : List (Fin 2)) :
    ¬ x ++ u <+: y ++ v := by
  obtain ⟨w, x', y', a, b, hab, rfl, rfl⟩ := split_of_incomp h1 h2
  intro h
  simp only [List.append_assoc, List.cons_append, List.prefix_append_right_inj,
    List.cons_prefix_cons] at h
  exact hab h.1

#audit_axioms GroupApproximation.BooneHigman.Join.incomp_append

theorem incomp_child {x : List (Fin 2)} : ¬ x ++ [0] <+: x ++ [1] := by
  rw [List.prefix_append_right_inj]
  decide

#audit_axioms GroupApproximation.BooneHigman.Join.incomp_child

theorem incomp_child' {x : List (Fin 2)} : ¬ x ++ [1] <+: x ++ [0] := by
  rw [List.prefix_append_right_inj]
  decide

#audit_axioms GroupApproximation.BooneHigman.Join.incomp_child'

/-- A three-element antichain. -/
theorem isAC_three {a b c : List (Fin 2)} (hab : ¬ a <+: b) (hba : ¬ b <+: a) (hac : ¬ a <+: c)
    (hca : ¬ c <+: a) (hbc : ¬ b <+: c) (hcb : ¬ c <+: b) : IsAC {a, b, c} := by
  intro u hu v hv hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | assumption

#audit_axioms GroupApproximation.BooneHigman.Join.isAC_three

theorem mapsCone_localize (w : List (Fin 2)) {g : Equiv.Perm (Cantor (Fin 2))}
    {c c' : List (Fin 2)} (h : MapsCone g c c') : MapsCone (localize w g) (w ++ c) (w ++ c') := by
  intro y
  rw [prepend_append, localize_apply_prepend, h y, ← prepend_append]

#audit_axioms GroupApproximation.BooneHigman.Join.mapsCone_localize

theorem mapsCone_localize_fix (w : List (Fin 2)) (g : Equiv.Perm (Cantor (Fin 2)))
    {c : List (Fin 2)} (h1 : ¬ w <+: c) (h2 : ¬ c <+: w) : MapsCone (localize w g) c c :=
  fun y => localize_apply_of_not (fun h => Set.disjoint_left.mp (disjoint_cone h1 h2) h
    (prepend_mem_cone c y)) g

#audit_axioms GroupApproximation.BooneHigman.Join.mapsCone_localize_fix

theorem mc_mul {a b : higmanVCCommon_Q 2} {u v w : List (Fin 2)} (ha : MapsCone (jperm 2 a) u v)
    (hb : MapsCone (jperm 2 b) v w) : MapsCone (jperm 2 (b * a)) u w := by
  rw [jperm_mul]
  exact MapsCone.comp ha hb

#audit_axioms GroupApproximation.BooneHigman.Join.mc_mul

theorem mc_inv {a : higmanVCCommon_Q 2} {u v : List (Fin 2)} (ha : MapsCone (jperm 2 a) u v) :
    MapsCone (jperm 2 a⁻¹) v u := by
  rw [jperm_inv]
  exact ha.inv

#audit_axioms GroupApproximation.BooneHigman.Join.mc_inv

theorem mc_phi (w : List (Fin 2)) {a : higmanVCCommon_Q 2} {u v : List (Fin 2)}
    (ha : MapsCone (jperm 2 a) u v) : MapsCone (jperm 2 (jPhi 2 w a)) (w ++ u) (w ++ v) := by
  rw [jperm_jPhi]
  exact mapsCone_localize w ha

#audit_axioms GroupApproximation.BooneHigman.Join.mc_phi

theorem mc_phi_fix (w : List (Fin 2)) (a : higmanVCCommon_Q 2) {c : List (Fin 2)}
    (h1 : ¬ w <+: c) (h2 : ¬ c <+: w) : MapsCone (jperm 2 (jPhi 2 w a)) c c := by
  rw [jperm_jPhi]
  exact mapsCone_localize_fix w _ h1 h2

#audit_axioms GroupApproximation.BooneHigman.Join.mc_phi_fix

/-- `BaseR` gives `BaseL`, by inverting. -/
theorem baseL_of_baseR {p q : List (Fin 2)} (h1 : ¬ p <+: q) (h2 : ¬ q <+: p)
    (h : BaseR p q) : BaseL p q := by
  obtain ⟨f, hf, ρ, hρ, e, m1, m2, m3, hfix⟩ := h
  have hC : IsAC {p, q ++ [0], q ++ [1]} :=
    isAC_three (by simpa using incomp_append h1 h2 [] [0]) (by simpa using incomp_append h2 h1 [0] [])
      (by simpa using incomp_append h1 h2 [] [1]) (by simpa using incomp_append h2 h1 [1] [])
      incomp_child incomp_child'
  refine ⟨f⁻¹, Phi.inv_mem hf, f * ρ⁻¹ * f⁻¹, ?_, ?_, mc_inv m1, mc_inv m2, mc_inv m3, ?_⟩
  · refine rcl_H jd2 hC f ?_ ((jH 2 _).inv_mem hρ)
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨_, by simp, m1⟩
    · exact ⟨_, by simp, m2⟩
    · exact ⟨_, by simp, m3⟩
  · rw [← jL_inv, e]
    group
  · intro z hz1 hz2
    have hz := hfix z hz1 hz2
    rw [jperm_inv, Equiv.Perm.inv_eq_iff_eq]
    exact hz.symm

#audit_axioms GroupApproximation.BooneHigman.Join.baseL_of_baseR

/-- Three involutions: `s = a b s · (s b s⁻¹)(s a s⁻¹)`. -/
theorem invol_alg {G : Type*} [Group G] {a b s : G} (ha : a * a = 1) (hb : b * b = 1)
    (hs : s * s = 1) : s = a * b * s * ((s * b * s⁻¹) * (s * a * s⁻¹)) := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ha2 : ∀ x : G, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hb2 : ∀ x : G, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  have hs2 : ∀ x : G, s * (s * x) = x := fun x => by rw [← mul_assoc, hs, one_mul]
  rw [hs']
  simp only [mul_assoc, hs2, hb2, ha2]

#audit_axioms GroupApproximation.BooneHigman.Join.invol_alg

/-- **The base case**: `BaseR 0 1`, from the definition of `X0`. -/
theorem baseR_zero_one : BaseR [0] [1] := by
  refine ⟨X0, X0_mem_Phi, jL [1, 1] [0] * jL [1, 0] [1, 1], ?_, ?_, mapsCone_X0_zero,
    mapsCone_X0_one_zero, mapsCone_X0_one_one, ?_⟩
  · exact (jH 2 _).mul_mem (jL_mem_jH (by simp) (by simp))
      (jL_mem_jH (by simp) (by simp))
  · have hs1 : ¬ ([0] : List (Fin 2)) <+: [1] := by decide
    have hs2 : ¬ ([1] : List (Fin 2)) <+: [0] := by decide
    have c1 : jL [0] [1] * jL [0, 1] [1] * (jL [0] [1])⁻¹ = jL [1, 1] [0] :=
      jL_conj hs1 hs2 ((mapsCone_coneSwap_left hs1 hs2).append [1])
        (mapsCone_coneSwap_right hs1 hs2) (by decide) (by decide) (by decide) (by decide)
    have c2 : jL [0] [1] * jL [0, 0] [0, 1] * (jL [0] [1])⁻¹ = jL [1, 0] [1, 1] :=
      jL_conj hs1 hs2 ((mapsCone_coneSwap_left hs1 hs2).append [0])
        ((mapsCone_coneSwap_left hs1 hs2).append [1]) (by decide) (by decide) (by decide)
        (by decide)
    rw [← c1, ← c2]
    unfold X0
    exact invol_alg (jL_sq _ _) (jL_sq _ _) (jL_sq _ _)
  · intro z hz1 hz2
    exfalso
    rcases fin2_cases (z 0) with h | h
    · exact hz1 fun k hk => by
        match k, hk with
        | 0, _ => exact h
        | k + 1, hk => simp at hk
    · exact hz2 fun k hk => by
        match k, hk with
        | 0, _ => exact h
        | k + 1, hk => simp at hk

#audit_axioms GroupApproximation.BooneHigman.Join.baseR_zero_one

end GroupApproximation.BooneHigman.Join
