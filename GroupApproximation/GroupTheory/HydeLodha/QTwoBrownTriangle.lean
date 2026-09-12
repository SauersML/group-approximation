import GroupApproximation.GroupTheory.HydeLodha.QTwoBrownStab
import GroupApproximation.GroupTheory.HydeLodha.GammaTwoCoreMoves
import GroupApproximation.GroupTheory.HigmanThompson.Orbits
import GroupApproximation.Meta.AxiomGuard

/-!
# The triangle condition for Hyde–Lodha's Theorem 4.8

Brown's criterion (`DoubleCosetFinitePresentation`) at the vertex `0 + ℤ` asks, for every pair
`t', t ∈ Γ`, that `H = vertexH Γ` is a finite union of double cosets
`(H ∩ t'⁻¹ H t') a₀ (H ∩ t H t⁻¹)` (`vertexH_triangle`).

The invariant of `a ∈ H` is the class of `x = fract (a (t 0))` relative to `p = fract (t'⁻¹ 0)`:
`x = 0`, `x = p`, or `x` in `(0, p)` resp. `(p, 1)` together with its residue modulo `5 ℤ[1/6]`
(`HigmanThompson.exists_resEq_unit`), at most twelve classes.  Two elements with the same invariant
differ on the left by the periodic copy `c` of an element of `F_6'` supported in a window
`[α, β] ⊆ (0, p)` resp. `(p, 1)` (Hyde–Lodha, Proposition 3.5, localized:
`exists_commutator_compactCore_move`), so `c` fixes `0` and `t'⁻¹ 0`, and on the right by
`d = a₀⁻¹ c⁻¹ a`, which fixes the class of `t 0`.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson DoubleCosetPresentation

/-! ## Moves of `F_6'` inside a window -/

/-- **Proposition 3.5 in a window.**  For grid points `0 < α < x, y < β < 1` with `x ≡ y` modulo
`5 ℤ[1/6]`, some element of `F_6' = ⁅core, core⁆` fixes `(-∞, α]` and `[β, ∞)` and sends `x` to `y`. -/
theorem exists_commutator_compactCore_move {α β x y : ℚ}
    (hα : ∃ M, α ∈ Grid (4 + 2) M) (hβ : ∃ M, β ∈ Grid (4 + 2) M)
    (hres : ResEq 4 y x) (h0α : 0 < α) (hαx : α < x) (hαy : α < y) (hxβ : x < β) (hyβ : y < β)
    (hβ1 : β < 1) :
    ∃ e ∈ ⁅compactCore 4, compactCore 4⁆,
      (∀ u, u ≤ α → e u = u) ∧ (∀ u, β ≤ u → e u = u) ∧ e x = y := by
  have hm1 := min_le_left x y
  have hm2 := min_le_right x y
  have hM1 := le_max_left x y
  have hM2 := le_max_right x y
  obtain ⟨α₁, hα₁a, hα₁b, hα₁⟩ := exists_grid_mem_Ioo (m := 4) (lt_min hαx hαy)
  obtain ⟨β₁, hβ₁a, hβ₁b, hβ₁⟩ := exists_grid_mem_Ioo (m := 4) (max_lt hxβ hyβ)
  -- the move `x ↦ y` inside `(α₁, β₁)`
  obtain ⟨f, hf, hflow, hfhigh, hfx⟩ := exists_move 4 hα₁ hβ₁ hres.symm (by linarith)
    (by linarith) (by linarith) (by linarith)
  have hfcore : f ∈ compactCore 4 :=
    move_mem_compactCore hf (by linarith) (by linarith) hflow hfhigh
  -- a displacing `z`, supported in `(α, β)`, with `z α₁ = c' > β₁`
  obtain ⟨c', hc'a, hc'b, hrc', hc'⟩ := exists_resEq_mem_Ioo (m := 4) hα₁ hβ₁b
  obtain ⟨d', hd'a, hd'b, hrd', hd'⟩ := exists_resEq_mem_Ioo (m := 4) hβ₁ hc'b
  obtain ⟨h₁, hh₁, h₁low, h₁high, h₁b⟩ := exists_move 4 hα₁ hβ hrd'.symm (by linarith)
    (by linarith) (by linarith) hd'b
  obtain ⟨h₂, hh₂, h₂low, h₂high, h₂a⟩ := exists_move 4 hα hd' hrc'.symm (by linarith)
    (by linarith) (by linarith) hd'a
  have hz : h₂ * h₁ ∈ compactCore 4 := (compactCore 4).mul_mem
    (move_mem_compactCore hh₂ h0α (by linarith) h₂low h₂high)
    (move_mem_compactCore hh₁ (by linarith) hβ1 h₁low h₁high)
  have hzα₁ : (h₂ * h₁) α₁ = c' := by
    rw [Equiv.Perm.mul_apply, h₁low α₁ le_rfl, h₂a]
  have hzlow : ∀ u, u ≤ α → (h₂ * h₁) u = u := fun u hu => by
    rw [Equiv.Perm.mul_apply, h₁low u (by linarith), h₂low u hu]
  have hzhigh : ∀ u, β ≤ u → (h₂ * h₁) u = u := fun u hu => by
    rw [Equiv.Perm.mul_apply, h₁high u hu, h₂high u (by linarith)]
  generalize h₂ * h₁ = z at hz hzα₁ hzlow hzhigh
  refine ⟨⁅f, z⁆, Subgroup.commutator_mem_commutator hfcore hz, ?_, ?_, ?_⟩
  · intro u hu
    have hzu : z⁻¹ u = u := perm_inv_eq_of_apply_eq (hzlow u hu)
    have hfu : f⁻¹ u = u := perm_inv_eq_of_apply_eq (hflow u (by linarith))
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    rw [hzu, hfu, hzlow u hu, hflow u (by linarith)]
  · intro u hu
    have hzu : z⁻¹ u = u := perm_inv_eq_of_apply_eq (hzhigh u hu)
    have hfu : f⁻¹ u = u := perm_inv_eq_of_apply_eq (hfhigh u (by linarith))
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    rw [hzu, hfu, hzhigh u hu, hfhigh u (by linarith)]
  · have hzx : z⁻¹ x ≤ α₁ := by
      by_contra hlt
      have h := compactF_strictMono (compactCore_le hz) (not_le.mp hlt)
      rw [hzα₁, perm_apply_inv_self] at h
      linarith
    have hfz : f⁻¹ (z⁻¹ x) = z⁻¹ x := perm_inv_eq_of_apply_eq (hflow _ hzx)
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    rw [hfz, perm_apply_inv_self, hfx]

#audit_axioms GroupApproximation.HydeLodha.exists_commutator_compactCore_move

end HydeLodha
end GroupApproximation
