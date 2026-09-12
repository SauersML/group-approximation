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
  obtain ⟨c', hc'a, hc'b, hrc', -⟩ := exists_resEq_mem_Ioo (m := 4) hα₁ hβ₁b
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

/-! ## The left factor -/

/-- **The periodic move in the edge stabilizer of `t'⁻¹`.**  For `x, y ∈ (0, 1)`, both different from
`p = fract (t'⁻¹ 0)`, on the same side of `p` and with `x ≡ y` modulo `5 ℤ[1/6]`, some
`c ∈ H ∩ t'⁻¹ H t'` sends every `s` with `fract s = x` to `⌊s⌋ + y`. -/
theorem exists_edgeStab_left {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo)
    (t' : ↥Γ) {x y : ℚ} (hres : ResEq 4 y x) (hx0 : 0 < x) (hy0 : 0 < y) (hx1 : x < 1)
    (hy1 : y < 1) (hxp : x ≠ Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0))
    (hyp : y ≠ Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0))
    (hside : Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) < x ↔
      Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) < y) :
    ∃ c : ↥(edgeStab (vertexH Γ) t'⁻¹), ∀ s : ℚ, Int.fract s = x →
      (((c : ↥(vertexH Γ)) : ↥Γ) : Equiv.Perm ℚ) s = ⌊s⌋ + y := by
  have hp0 : 0 ≤ Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) := Int.fract_nonneg _
  have hp1 : Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) < 1 := Int.fract_lt_one _
  have hm1 := min_le_left x y
  have hm2 := min_le_right x y
  have hM1 := le_max_left x y
  have hM2 := le_max_right x y
  obtain ⟨α, β, hα, hβ, h0α, hαx, hαy, hxβ, hyβ, hβ1, hpαβ⟩ : ∃ α β : ℚ,
      (∃ M, α ∈ Grid (4 + 2) M) ∧ (∃ M, β ∈ Grid (4 + 2) M) ∧ 0 < α ∧ α < x ∧ α < y ∧ x < β ∧
        y < β ∧ β < 1 ∧ (Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) ≤ α ∨
          β ≤ Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0)) := by
    rcases lt_or_gt_of_ne hxp with hxlt | hxgt
    · have hylt : y < Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) := by
        rcases lt_or_gt_of_ne hyp with h | h
        · exact h
        · exact absurd (hside.mpr h) (not_lt.mpr hxlt.le)
      obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := 4) (lt_min hx0 hy0)
      obtain ⟨β, hβ1, hβ2, hβ⟩ := exists_grid_mem_Ioo (m := 4) (max_lt hxlt hylt)
      exact ⟨α, β, hα, hβ, hα1, by linarith, by linarith, by linarith, by linarith, by linarith,
        Or.inr hβ2.le⟩
    · have hygt : Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) < y := hside.mp hxgt
      obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := 4) (lt_min hxgt hygt)
      obtain ⟨β, hβ1, hβ2, hβ⟩ := exists_grid_mem_Ioo (m := 4) (max_lt hx1 hy1)
      exact ⟨α, β, hα, hβ, by linarith, by linarith, by linarith, by linarith, by linarith, hβ2,
        Or.inl hα1.le⟩
  obtain ⟨e, he, hlow, hhigh, hex⟩ :=
    exists_commutator_compactCore_move hα hβ hres h0α hαx hαy hxβ hyβ hβ1
  let eF : ↥(compactF 4 1) := ⟨e, compactCore_le (commutator_le_self _ he)⟩
  have hfix : ∀ s : ℚ, (Int.fract s ≤ α ∨ β ≤ Int.fract s) → perHom 4 eF s = s := by
    intro s hs
    rw [perHom_apply]
    rcases hs with hs | hs
    · rw [show (eF : Equiv.Perm ℚ) (Int.fract s) = Int.fract s from hlow _ hs, Int.floor_add_fract]
    · rw [show (eF : Equiv.Perm ℚ) (Int.fract s) = Int.fract s from hhigh _ hs,
        Int.floor_add_fract]
  have hcQ : perHom 4 eF ∈ qTwo :=
    commutator_perCore_le_qTwo (perHom_mem_commutator_perCore 4 he)
  let cΓ : ↥Γ := ⟨perHom 4 eF, hQ hcQ⟩
  have hcH : cΓ ∈ vertexH Γ := (mem_vertexH_iff hΓ).mpr ⟨0, by
    show perHom 4 eF 0 = 0 + ((0 : ℤ) : ℚ)
    rw [hfix 0 (Or.inl (by rw [Int.fract_zero]; exact h0α.le))]
    simp⟩
  refine ⟨⟨⟨cΓ, hcH⟩, (mem_edgeStab_vertexH_iff hΓ t'⁻¹ ⟨cΓ, hcH⟩).mpr ⟨0, ?_⟩⟩, fun s hs => ?_⟩
  · show perHom 4 eF (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0) =
      ((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0 + ((0 : ℤ) : ℚ)
    rw [hfix _ hpαβ]
    simp
  · show perHom 4 eF s = ⌊s⌋ + y
    rw [perHom_apply, hs]
    exact congrArg (fun w => (⌊s⌋ : ℚ) + w) hex

/-! ## The invariant -/

open Classical in
/-- A residue label in `Fin 5` for a point of `ℤ[1/6]` (`exists_resEq_unit`). -/
noncomputable def resLabel (x : ℚ) : Fin (4 + 1) :=
  if h : ∃ M, x ∈ Grid (4 + 2) M then Classical.choose (exists_resEq_unit 4 h) else 0

theorem resEq_of_resLabel_eq {x y : ℚ} (hx : ∃ M, x ∈ Grid (4 + 2) M)
    (hy : ∃ M, y ∈ Grid (4 + 2) M) (h : resLabel x = resLabel y) : ResEq 4 x y := by
  have h1 := Classical.choose_spec (exists_resEq_unit 4 hx)
  have h2 := Classical.choose_spec (exists_resEq_unit 4 hy)
  simp only [resLabel, dif_pos hx, dif_pos hy] at h
  rw [h] at h1
  exact h1.trans h2.symm

/-- The invariant of a point relative to `p`: `0`, `p`, or the side of `p` with the residue label. -/
noncomputable def triKey (p x : ℚ) : Fin 2 ⊕ (Bool × Fin (4 + 1)) :=
  if x = 0 then Sum.inl 0 else if x = p then Sum.inl 1 else Sum.inr (decide (p < x), resLabel x)

theorem triKey_eq {p x y : ℚ} (h : triKey p x = triKey p y) :
    x = y ∨ (x ≠ 0 ∧ y ≠ 0 ∧ x ≠ p ∧ y ≠ p ∧ (p < x ↔ p < y) ∧ resLabel x = resLabel y) := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  right
  have kr : ∀ z : ℚ, z ≠ 0 → z ≠ p → triKey p z = Sum.inr (decide (p < z), resLabel z) := by
    intro z hz0 hzp
    simp only [triKey, if_neg hz0, if_neg hzp]
  have k0 : triKey p 0 = Sum.inl 0 := by simp [triKey]
  have kp : ∀ z : ℚ, z ≠ 0 → z = p → triKey p z = Sum.inl 1 := by
    intro z hz0 hzp
    simp only [triKey, if_neg hz0, if_pos hzp]
  by_cases hx0 : x = 0
  · exfalso
    by_cases hy0 : y = 0
    · exact hxy (hx0.trans hy0.symm)
    rw [hx0, k0] at h
    by_cases hyp : y = p
    · rw [kp y hy0 hyp] at h
      simp at h
    · rw [kr y hy0 hyp] at h
      simp at h
  by_cases hy0 : y = 0
  · exfalso
    rw [hy0, k0] at h
    by_cases hxp : x = p
    · rw [kp x hx0 hxp] at h
      simp at h
    · rw [kr x hx0 hxp] at h
      simp at h
  by_cases hxp : x = p
  · exfalso
    by_cases hyp : y = p
    · exact hxy (hxp.trans hyp.symm)
    rw [kp x hx0 hxp, kr y hy0 hyp] at h
    simp at h
  by_cases hyp : y = p
  · exfalso
    rw [kr x hx0 hxp, kp y hy0 hyp] at h
    simp at h
  rw [kr x hx0 hxp, kr y hy0 hyp] at h
  simp only [Sum.inr.injEq, Prod.mk.injEq, decide_eq_decide] at h
  exact ⟨hx0, hy0, hxp, hyp, h.1, h.2⟩

/-! ## The triangle condition -/

/-- **Brown's triangle condition at the vertex `0 + ℤ`** (Hyde–Lodha, Theorem 4.8): for `t', t ∈ Γ`,
`H = vertexH Γ` is a finite union of double cosets `(H ∩ t'⁻¹ H t') a₀ (H ∩ t H t⁻¹)`. -/
theorem vertexH_triangle {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo)
    (t' t : ↥Γ) :
    ∃ A : Finset ↥(vertexH Γ), ∀ a : ↥(vertexH Γ),
      ∃ c : ↥(DoubleCosetPresentation.edgeStab (vertexH Γ) t'⁻¹),
      ∃ d : ↥(DoubleCosetPresentation.edgeStab (vertexH Γ) t),
      ∃ a₀ ∈ A, a = (c : ↥(vertexH Γ)) * a₀ * d := by
  classical
  let X : ↥(vertexH Γ) → ℚ := fun a =>
    Int.fract (((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0))
  let key : ↥(vertexH Γ) → Fin 2 ⊕ (Bool × Fin (4 + 1)) := fun a =>
    triKey (Int.fract (((t'⁻¹ : ↥Γ) : Equiv.Perm ℚ) 0)) (X a)
  let rep : Fin 2 ⊕ (Bool × Fin (4 + 1)) → ↥(vertexH Γ) := fun l =>
    if h : ∃ a, key a = l then Classical.choose h else 1
  refine ⟨Finset.univ.image rep, fun a => ?_⟩
  have hex : ∃ a', key a' = key a := ⟨a, rfl⟩
  have hrep : key (rep (key a)) = key a := by
    show key (if h : ∃ a', key a' = key a then Classical.choose h else 1) = key a
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hmem : rep (key a) ∈ Finset.univ.image rep :=
    Finset.mem_image_of_mem rep (Finset.mem_univ (key a))
  generalize rep (key a) = a₀ at hrep hmem
  have hgrid : ∀ b : ↥(vertexH Γ), ∃ M, X b ∈ Grid (4 + 2) M := fun b =>
    fract_grid (gammaTwo_apply_grid (hΓ (b : ↥Γ).2)
      (gammaTwo_apply_grid (hΓ t.2) zero_mem_grid_six))
  have hleft : ∃ c : ↥(edgeStab (vertexH Γ) t'⁻¹), ∃ j : ℤ,
      (((c : ↥(vertexH Γ)) : ↥Γ) : Equiv.Perm ℚ) (((a₀ : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0)) =
        ((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) + j := by
    rcases triKey_eq hrep with hxy | ⟨hx0, hy0, hxp, hyp, hside, hlab⟩
    · obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hxy
      refine ⟨1, z, ?_⟩
      show ((a₀ : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) =
        ((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) + z
      linarith
    · have hres : ResEq 4 (X a) (X a₀) := resEq_of_resLabel_eq (hgrid a) (hgrid a₀) hlab.symm
      obtain ⟨c, hc⟩ := exists_edgeStab_left hQ hΓ t' hres
        (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hx0))
        (lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hy0)) (Int.fract_lt_one _)
        (Int.fract_lt_one _) hxp hyp hside
      refine ⟨c, ⌊((a₀ : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0)⌋ -
        ⌊((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0)⌋, ?_⟩
      rw [hc (((a₀ : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0)) rfl]
      have h1 : (⌊((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0)⌋ : ℚ) + X a =
          ((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) := Int.floor_add_fract _
      push_cast
      linarith
  obtain ⟨c, j, hcj⟩ := hleft
  have hdmem : (a₀⁻¹ * (c : ↥(vertexH Γ))⁻¹ * a : ↥(vertexH Γ)) ∈ edgeStab (vertexH Γ) t := by
    rw [mem_edgeStab_vertexH_iff hΓ t]
    refine ⟨-j, ?_⟩
    show ((a₀ : ↥Γ) : Equiv.Perm ℚ)⁻¹ ((((c : ↥(vertexH Γ)) : ↥Γ) : Equiv.Perm ℚ)⁻¹
        (((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0))) =
      (t : Equiv.Perm ℚ) 0 + ((-j : ℤ) : ℚ)
    have hcΓ : (((c : ↥(vertexH Γ)) : ↥Γ) : Equiv.Perm ℚ) ∈ gammaTwo :=
      hΓ ((c : ↥(vertexH Γ)) : ↥Γ).2
    have ha₀Γ : ((a₀ : ↥Γ) : Equiv.Perm ℚ)⁻¹ ∈ gammaTwo := gammaTwo.inv_mem (hΓ (a₀ : ↥Γ).2)
    have h1 : (((c : ↥(vertexH Γ)) : ↥Γ) : Equiv.Perm ℚ)
        (((a₀ : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) + ((-j : ℤ) : ℚ)) =
          ((a : ↥Γ) : Equiv.Perm ℚ) ((t : Equiv.Perm ℚ) 0) := by
      rw [gammaTwo_add_int hcΓ, hcj]
      push_cast
      ring
    rw [perm_inv_eq_of_apply_eq h1, gammaTwo_add_int ha₀Γ, perm_inv_apply_self]
  refine ⟨c, ⟨_, hdmem⟩, a₀, hmem, ?_⟩
  show a = (c : ↥(vertexH Γ)) * a₀ * (a₀⁻¹ * (c : ↥(vertexH Γ))⁻¹ * a)
  group

#audit_axioms GroupApproximation.HydeLodha.exists_commutator_compactCore_move
#audit_axioms GroupApproximation.HydeLodha.exists_edgeStab_left
#audit_axioms GroupApproximation.HydeLodha.triKey_eq
#audit_axioms GroupApproximation.HydeLodha.vertexH_triangle

end HydeLodha
end GroupApproximation
