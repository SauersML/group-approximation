import GroupApproximation.GroupTheory.HydeLodha.QTwoBrownStab
import GroupApproximation.GroupTheory.HydeLodha.GammaTwoCoreMoves
import GroupApproximation.GroupTheory.HigmanThompson.Orbits
import GroupApproximation.Meta.AxiomGuard

/-!
# Finitely many double cosets of the vertex stabilizer

Hyde–Lodha, Theorem 4.8: "From Proposition 3.5, for each `k ∈ ℕ ∖ {0}`, the action of `F_{η_n}'` on
`(ℤ[1/η_n])^k` has finitely many orbits.  Hence the same holds for `Γ` since `F_{η_n}' ≤ Q_n ≤ Γ`."

For the vertex `0 + ℤ` of `X = ℤ[1/6]/ℤ` this is the cover of `Γ` by finitely many double cosets
`H t H`, `H = vertexH Γ` (`vertexH_cover`): the double coset of `g` is determined by `cosetClass g`,
which records whether `g 0 ∈ ℤ` and otherwise the residue class of `fract (g 0)` modulo `5 ℤ[1/6]`.
If `g` and `t` have the same class, the periodic `F_6'` moves `t 0` to `g 0` modulo `ℤ`
(`exists_perCore_apply`), so `g = a t b` with `a, b ∈ H`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson DoubleCosetPresentation

open Classical in
/-- The invariant of the double coset `H g H`. -/
noncomputable def cosetClass (g : Equiv.Perm ℚ) : Option (Fin (4 + 1)) :=
  if h : 0 < Int.fract (g 0) ∧ ∃ M, Int.fract (g 0) ∈ Grid (4 + 2) M then
    some (Classical.choose (exists_resEq_unit 4 h.2)) else none

theorem cosetClass_spec {g : Equiv.Perm ℚ} (h0 : 0 < Int.fract (g 0))
    (hg : ∃ M, Int.fract (g 0) ∈ Grid (4 + 2) M) :
    ∃ j : Fin (4 + 1), cosetClass g = some j ∧
      ResEq 4 (Int.fract (g 0)) (((j : ℕ) + 1 : ℚ) / (((4 : ℕ) : ℚ) + 2)) := by
  refine ⟨Classical.choose (exists_resEq_unit 4 hg), ?_, Classical.choose_spec (exists_resEq_unit 4 hg)⟩
  simp only [cosetClass, dif_pos (And.intro h0 hg)]

theorem cosetClass_of_not_pos {g : Equiv.Perm ℚ} (h0 : ¬ 0 < Int.fract (g 0)) : cosetClass g = none := by
  simp only [cosetClass, dif_neg (fun h : 0 < Int.fract (g 0) ∧ _ => h0 h.1)]

variable {Γ : Subgroup (Equiv.Perm ℚ)}

theorem mem_vertexH_of_fract_eq_zero (hΓ : Γ ≤ gammaTwo) {g : ↥Γ}
    (h0 : ¬ 0 < Int.fract ((g : Equiv.Perm ℚ) 0)) : g ∈ vertexH Γ := by
  rw [mem_vertexH_iff hΓ]
  have hfr : Int.fract ((g : Equiv.Perm ℚ) 0) = 0 :=
    le_antisymm (not_lt.mp h0) (Int.fract_nonneg _)
  refine ⟨⌊(g : Equiv.Perm ℚ) 0⌋, ?_⟩
  have e := Int.floor_add_fract ((g : Equiv.Perm ℚ) 0)
  rw [hfr, add_zero] at e
  rw [zero_add, e]

/-- **Finitely many double cosets `H t H`.** -/
theorem vertexH_cover (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) :
    ∃ T : Finset ↥Γ, ∀ g : ↥Γ, ∃ t ∈ T, ∃ a b : ↥(vertexH Γ), g = (a : ↥Γ) * t * b := by
  classical
  let rep : Option (Fin (4 + 1)) → ↥Γ := fun σ =>
    if h : ∃ g : ↥Γ, cosetClass (g : Equiv.Perm ℚ) = σ then Classical.choose h else 1
  refine ⟨Finset.univ.image rep, fun g => ?_⟩
  have hex : ∃ g' : ↥Γ, cosetClass (g' : Equiv.Perm ℚ) = cosetClass (g : Equiv.Perm ℚ) :=
    ⟨g, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : ↥Γ, t = rep (cosetClass (g : Equiv.Perm ℚ)) := ⟨_, rfl⟩
  have htc : cosetClass (t : Equiv.Perm ℚ) = cosetClass (g : Equiv.Perm ℚ) := by
    rw [htdef]
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  refine ⟨t, by rw [htdef]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hgG : ∃ M, Int.fract ((g : Equiv.Perm ℚ) 0) ∈ Grid (4 + 2) M :=
    fract_grid (gammaTwo_apply_grid (hΓ g.2) zero_mem_grid_six)
  have htG : ∃ M, Int.fract ((t : Equiv.Perm ℚ) 0) ∈ Grid (4 + 2) M :=
    fract_grid (gammaTwo_apply_grid (hΓ t.2) zero_mem_grid_six)
  by_cases hg0 : 0 < Int.fract ((g : Equiv.Perm ℚ) 0)
  · obtain ⟨j, hj, hjres⟩ := cosetClass_spec hg0 hgG
    have ht0 : 0 < Int.fract ((t : Equiv.Perm ℚ) 0) := by
      by_contra hn
      have hnone := cosetClass_of_not_pos hn
      rw [htc, hj] at hnone
      exact Option.some_ne_none _ hnone
    obtain ⟨j', hj', hj'res⟩ := cosetClass_spec ht0 htG
    rw [htc, hj] at hj'
    have hjj : j = j' := Option.some_injective _ hj'
    subst hjj
    have hres : ResEq 4 (Int.fract ((g : Equiv.Perm ℚ) 0)) (Int.fract ((t : Equiv.Perm ℚ) 0)) :=
      hjres.trans hj'res.symm
    obtain ⟨p, hpK, hpx⟩ := exists_perCore_apply htG hgG hres ht0 (Int.fract_lt_one _) hg0
      (Int.fract_lt_one _)
    have haΓ : perHom 4 p ∈ Γ := hQ (commutator_perCore_le_qTwo hpK)
    have haG := hΓ haΓ
    have hht := hΓ (Γ.inv_mem t.2)
    obtain ⟨k, hkdef⟩ : ∃ k : ℤ, k = ⌊(g : Equiv.Perm ℚ) 0⌋ - ⌊(t : Equiv.Perm ℚ) 0⌋ := ⟨_, rfl⟩
    have hat : perHom 4 p ((t : Equiv.Perm ℚ) 0 + k) = (g : Equiv.Perm ℚ) 0 := by
      have e1 := perHom_add_int 4 p (Int.fract ((t : Equiv.Perm ℚ) 0)) (⌊(t : Equiv.Perm ℚ) 0⌋ + k)
      have e2 : Int.fract ((t : Equiv.Perm ℚ) 0) + (((⌊(t : Equiv.Perm ℚ) 0⌋ + k : ℤ)) : ℚ) =
          (t : Equiv.Perm ℚ) 0 + k := by
        push_cast
        linarith [Int.fract_add_floor ((t : Equiv.Perm ℚ) 0)]
      rw [e2, hpx] at e1
      rw [e1, hkdef]
      push_cast
      linarith [Int.fract_add_floor ((g : Equiv.Perm ℚ) 0)]
    have hainv : (perHom 4 p)⁻¹ ((g : Equiv.Perm ℚ) 0) = (t : Equiv.Perm ℚ) 0 + k :=
      perm_inv_eq_of_apply_eq hat
    have hb0 : (t : Equiv.Perm ℚ)⁻¹ ((perHom 4 p)⁻¹ ((g : Equiv.Perm ℚ) 0)) = 0 + k := by
      rw [hainv, gammaTwo_add_int hht, perm_inv_apply_self]
    let a : ↥Γ := ⟨perHom 4 p, haΓ⟩
    have ha : a ∈ vertexH Γ := by
      rw [mem_vertexH_iff hΓ]
      refine ⟨0, ?_⟩
      show perHom 4 p 0 = 0 + ((0 : ℤ) : ℚ)
      have h := perHom_apply_intCast p 0
      rw [Int.cast_zero] at h
      rw [Int.cast_zero, add_zero]
      exact h
    have hb : t⁻¹ * a⁻¹ * g ∈ vertexH Γ := by
      rw [mem_vertexH_iff hΓ]
      exact ⟨k, hb0⟩
    refine ⟨⟨a, ha⟩, ⟨t⁻¹ * a⁻¹ * g, hb⟩, ?_⟩
    show g = a * t * (t⁻¹ * a⁻¹ * g)
    group
  · have hgH := mem_vertexH_of_fract_eq_zero hΓ hg0
    have ht0 : ¬ 0 < Int.fract ((t : Equiv.Perm ℚ) 0) := by
      intro hpos
      obtain ⟨j, hj, -⟩ := cosetClass_spec hpos htG
      rw [htc, cosetClass_of_not_pos hg0] at hj
      exact Option.some_ne_none _ hj.symm
    have htH := mem_vertexH_of_fract_eq_zero hΓ ht0
    refine ⟨⟨g * t⁻¹, (vertexH Γ).mul_mem hgH ((vertexH Γ).inv_mem htH)⟩, 1, ?_⟩
    show g = g * t⁻¹ * t * 1
    group

#audit_axioms GroupApproximation.HydeLodha.vertexH_cover

end HydeLodha
end GroupApproximation
