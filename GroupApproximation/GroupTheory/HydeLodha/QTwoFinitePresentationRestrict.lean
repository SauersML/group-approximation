import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationDefs
import GroupApproximation.GroupTheory.HydeLodha.GammaTwoStabilizer
import GroupApproximation.Meta.AxiomGuard

/-!
# Restricting an element of `Γ₂` to `[c, d] + ℤ`

Hyde–Lodha, proof of Proposition 4.7: for `K` with `max(K) < min(K) + 1` the left closed, right open
intervals `L_1, …, L_{|K|}` between consecutive points of `K + ℤ` give `Γ_K ⊆ R = ∏ Rstab_{Γ_n}(L_j)`.
That inclusion is the statement that an element of `Γ₂` fixing two points `c, d` restricts to
`[c, d] + ℤ`:

* `perIcc c d`: the periodic closed set `[c, d] + ℤ`;
* `perRestrict f c d`: `f` on `[c, d] + ℤ`, the identity elsewhere;
* `gridInterval_cases`: for `c, d` of level `N`, every level-`N` grid interval lies in a translate of
  `[c, d]` or meets `[c, d] + ℤ` only in points of `c + ℤ` and `d + ℤ`;
* `perRestrictPerm_mem_gammaTwo`: for `f ∈ Γ₂` fixing `c, d ∈ ℤ[1/6]`, the restriction is in `Γ₂`;
* `exists_upsilon_split`: an element of `Υ_{Γ₂}([c, e])` fixing `c` and `d` is `f₁ f₂` with
  `f₁ ∈ Υ_{Γ₂}([c, d])` equal to `f` on `[c, d]` and `f₂ ∈ Υ_{Γ₂}([d, e])`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-- `[c, d] + ℤ`. -/
def perIcc (c d : ℚ) : Set ℚ := {t | ∃ k : ℤ, c ≤ t + k ∧ t + k ≤ d}

theorem mem_perIcc_add_one {c d t : ℚ} : t + 1 ∈ perIcc c d ↔ t ∈ perIcc c d := by
  constructor
  · rintro ⟨k, h1, h2⟩
    refine ⟨k + 1, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨k, h1, h2⟩
    refine ⟨k - 1, ?_, ?_⟩ <;> push_cast <;> linarith

/-! ## Grid intervals -/

theorem gridPt_six_le_succ (N : ℕ) (k : ℤ) : gridPt 6 N k ≤ gridPt 6 N (k + 1) := by
  have hstep : gridPt 6 N (k + 1) = gridPt 6 N k + ((6 : ℚ) ^ N)⁻¹ := by
    unfold gridPt
    push_cast
    ring
  have hpos : (0 : ℚ) < ((6 : ℚ) ^ N)⁻¹ := by positivity
  linarith

theorem exists_gridPt_bracket_of_not_dyadic6 (N : ℕ) {x : ℚ} (hx : ¬ Dyadic6 x) :
    ∃ k : ℤ, gridPt 6 N k < x ∧ x < gridPt 6 N (k + 1) := by
  obtain ⟨h1, h2⟩ := floor_bracket (m := 6) N x
  refine ⟨_, lt_of_le_of_ne h1 fun h => hx ⟨N, ?_⟩, h2⟩
  rw [← h]
  exact gridPt_mem N _

/-- Every level-`N` grid interval lies in a translate of `[c, d]`, or meets `[c, d] + ℤ` only in
`c + ℤ` and `d + ℤ`. -/
theorem gridInterval_cases {c d : ℚ} {N : ℕ} (hc : c ∈ Grid 6 N) (hd : d ∈ Grid 6 N) (k : ℤ) :
    (∃ j : ℤ, c ≤ gridPt 6 N k + j ∧ gridPt 6 N (k + 1) + j ≤ d) ∨
      ∀ t, gridPt 6 N k ≤ t → t ≤ gridPt 6 N (k + 1) → t ∈ perIcc c d →
        (∃ j : ℤ, t + j = c) ∨ ∃ j : ℤ, t + j = d := by
  have hstep : gridPt 6 N (k + 1) = gridPt 6 N k + ((6 : ℚ) ^ N)⁻¹ := by
    unfold gridPt
    push_cast
    ring
  have hpos : (0 : ℚ) < ((6 : ℚ) ^ N)⁻¹ := by positivity
  have hcj : ∀ j : ℤ, ¬ (gridPt 6 N k < c - j ∧ c - j < gridPt 6 N (k + 1)) := fun j =>
    not_between_consecutive (grid_sub hc (int_mem_grid N j))
  have hdj : ∀ j : ℤ, ¬ (gridPt 6 N k < d - j ∧ d - j < gridPt 6 N (k + 1)) := fun j =>
    not_between_consecutive (grid_sub hd (int_mem_grid N j))
  by_cases hq : (gridPt 6 N k + gridPt 6 N (k + 1)) / 2 ∈ perIcc c d
  · obtain ⟨j, hj1, hj2⟩ := hq
    left
    refine ⟨j, ?_, ?_⟩
    · by_contra h
      rw [not_le] at h
      exact hcj j ⟨by linarith, by linarith⟩
    · by_contra h
      rw [not_le] at h
      exact hdj j ⟨by linarith, by linarith⟩
  · right
    intro t ht1 ht2 ht
    obtain ⟨j, hj1, hj2⟩ := ht
    have hq' : ¬ (c ≤ (gridPt 6 N k + gridPt 6 N (k + 1)) / 2 + j ∧
        (gridPt 6 N k + gridPt 6 N (k + 1)) / 2 + j ≤ d) := fun h => hq ⟨j, h.1, h.2⟩
    rcases not_and_or.mp hq' with h | h
    · rw [not_le] at h
      left
      refine ⟨j, ?_⟩
      rcases lt_or_eq_of_le hj1 with hlt | heq
      · exact (hcj j ⟨by linarith, by linarith⟩).elim
      · exact heq.symm
    · rw [not_le] at h
      right
      refine ⟨j, ?_⟩
      rcases lt_or_eq_of_le hj2 with hlt | heq
      · exact (hdj j ⟨by linarith, by linarith⟩).elim
      · exact heq

/-! ## The restriction -/

open Classical in
/-- `f` on `[c, d] + ℤ`, the identity elsewhere. -/
noncomputable def perRestrict (f : Equiv.Perm ℚ) (c d t : ℚ) : ℚ :=
  if t ∈ perIcc c d then f t else t

theorem perRestrict_of_mem {f : Equiv.Perm ℚ} {c d t : ℚ} (h : t ∈ perIcc c d) :
    perRestrict f c d t = f t := by
  rw [perRestrict, if_pos h]

theorem perRestrict_of_not_mem {f : Equiv.Perm ℚ} {c d t : ℚ} (h : t ∉ perIcc c d) :
    perRestrict f c d t = t := by
  rw [perRestrict, if_neg h]

theorem perm_inv_apply_of_fix {f : Equiv.Perm ℚ} {c : ℚ} (h : f c = c) : f⁻¹ c = c := by
  rw [Equiv.Perm.inv_eq_iff_eq, h]

section Restrict

variable {f : Equiv.Perm ℚ} {c d : ℚ}

theorem apply_add_int_mem_Icc (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) {t : ℚ} {k : ℤ}
    (h1 : c ≤ t + k) (h2 : t + k ≤ d) : c ≤ f t + k ∧ f t + k ≤ d := by
  have hmono := (gammaTwo_strictMono hf).monotone
  have e := gammaTwo_add_int hf t k
  constructor
  · have h := hmono h1
    rwa [hc, e] at h
  · have h := hmono h2
    rwa [hd, e] at h

theorem mem_perIcc_apply (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) {t : ℚ}
    (ht : t ∈ perIcc c d) : f t ∈ perIcc c d := by
  obtain ⟨k, h1, h2⟩ := ht
  exact ⟨k, apply_add_int_mem_Icc hf hc hd h1 h2⟩

theorem mem_perIcc_apply_iff (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) {t : ℚ} :
    f t ∈ perIcc c d ↔ t ∈ perIcc c d := by
  refine ⟨fun h => ?_, mem_perIcc_apply hf hc hd⟩
  have h' := mem_perIcc_apply (gammaTwo.inv_mem hf) (perm_inv_apply_of_fix hc)
    (perm_inv_apply_of_fix hd) h
  rwa [perm_inv_apply_self] at h'

theorem perRestrict_left_inv (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) (t : ℚ) :
    perRestrict f⁻¹ c d (perRestrict f c d t) = t := by
  by_cases ht : t ∈ perIcc c d
  · rw [perRestrict_of_mem ht, perRestrict_of_mem (mem_perIcc_apply hf hc hd ht),
      perm_inv_apply_self]
  · rw [perRestrict_of_not_mem ht, perRestrict_of_not_mem ht]

theorem perRestrict_right_inv (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) (t : ℚ) :
    perRestrict f c d (perRestrict f⁻¹ c d t) = t := by
  have h := perRestrict_left_inv (gammaTwo.inv_mem hf) (perm_inv_apply_of_fix hc)
    (perm_inv_apply_of_fix hd) t
  rwa [inv_inv] at h

/-- The restriction as a permutation. -/
noncomputable def perRestrictPerm (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) :
    Equiv.Perm ℚ where
  toFun := perRestrict f c d
  invFun := perRestrict f⁻¹ c d
  left_inv := perRestrict_left_inv hf hc hd
  right_inv := perRestrict_right_inv hf hc hd

theorem perRestrict_strictMono (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) :
    StrictMono (perRestrict f c d) := by
  have hmono := gammaTwo_strictMono hf
  intro s t hst
  by_cases hs : s ∈ perIcc c d
  · by_cases ht : t ∈ perIcc c d
    · rw [perRestrict_of_mem hs, perRestrict_of_mem ht]
      exact hmono hst
    · rw [perRestrict_of_mem hs, perRestrict_of_not_mem ht]
      obtain ⟨k, hk1, hk2⟩ := hs
      have hfs := apply_add_int_mem_Icc hf hc hd hk1 hk2
      have htk : d < t + k := by
        by_contra h
        exact ht ⟨k, by linarith, not_lt.mp h⟩
      linarith [hfs.2]
  · by_cases ht : t ∈ perIcc c d
    · rw [perRestrict_of_not_mem hs, perRestrict_of_mem ht]
      obtain ⟨k, hk1, hk2⟩ := ht
      have hft := apply_add_int_mem_Icc hf hc hd hk1 hk2
      have hsk : s + k < c := by
        by_contra h
        exact hs ⟨k, not_lt.mp h, by linarith⟩
      linarith [hft.1]
    · rw [perRestrict_of_not_mem hs, perRestrict_of_not_mem ht]
      exact hst

/-- At a point of `[c, d] + ℤ` lying in `c + ℤ` or `d + ℤ`, the restriction is the identity. -/
theorem perRestrict_eq_self_of_boundary (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d)
    {t : ℚ} (h : t ∈ perIcc c d → (∃ j : ℤ, t + j = c) ∨ ∃ j : ℤ, t + j = d) :
    perRestrict f c d t = t := by
  by_cases ht : t ∈ perIcc c d
  · rw [perRestrict_of_mem ht]
    rcases h ht with ⟨j, hj⟩ | ⟨j, hj⟩
    · have e := gammaTwo_add_int hf t j
      rw [hj, hc] at e
      linarith
    · have e := gammaTwo_add_int hf t j
      rw [hj, hd] at e
      linarith
  · exact perRestrict_of_not_mem ht

theorem perRestrict_add_one (hf : f ∈ gammaTwo) (t : ℚ) :
    perRestrict f c d (t + 1) = perRestrict f c d t + 1 := by
  by_cases ht : t ∈ perIcc c d
  · rw [perRestrict_of_mem ht, perRestrict_of_mem (mem_perIcc_add_one.mpr ht),
      (mem_gammaTwo.mp hf).2.1 t]
  · have ht' : t + 1 ∉ perIcc c d := fun h => ht (mem_perIcc_add_one.mp h)
    rw [perRestrict_of_not_mem ht, perRestrict_of_not_mem ht']

theorem perRestrict_gridAffine (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) {N B : ℕ}
    (hA : GridAffine 6 slopes23 f N B) (hcN : c ∈ Grid 6 N) (hdN : d ∈ Grid 6 N) (hNB : N ≤ B) :
    GridAffine 6 slopes23 (perRestrict f c d) N B := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have hle := gridPt_six_le_succ N k
    rcases gridInterval_cases hcN hdN k with ⟨j, hj1, hj2⟩ | hfix
    · obtain ⟨s, hsΩ, hsB, haff⟩ := hA.slope k
      refine ⟨s, hsΩ, hsB, fun x hx1 hx2 => ?_⟩
      have hx : x ∈ perIcc c d := ⟨j, by linarith, by linarith⟩
      have hp : gridPt 6 N k ∈ perIcc c d := ⟨j, hj1, by linarith⟩
      rw [perRestrict_of_mem hx, perRestrict_of_mem hp]
      exact haff x hx1 hx2
    · refine ⟨1, slopes23.one_mem, by simpa using int_mem_grid (m := 6) B 1, fun x hx1 hx2 => ?_⟩
      rw [perRestrict_eq_self_of_boundary hf hc hd (hfix x hx1 hx2),
        perRestrict_eq_self_of_boundary hf hc hd (hfix _ le_rfl (le_trans hx1 hx2))]
      ring
  · by_cases hp : gridPt 6 N k ∈ perIcc c d
    · rw [perRestrict_of_mem hp]
      exact hA.value k
    · rw [perRestrict_of_not_mem hp]
      exact grid_mono hNB (gridPt_mem N k)

theorem exists_perRestrict_gridAffine (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d)
    {Mc Md : ℕ} (hMc : c ∈ Grid 6 Mc) (hMd : d ∈ Grid 6 Md) :
    ∃ N B, GridAffine 6 slopes23 (perRestrict f c d) N B := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, -, -⟩ := mem_gammaTwo.mp hf
  exact ⟨max N (max Mc Md), B + max N (max Mc Md), perRestrict_gridAffine hf hc hd
    (hA.mono_level (le_max_left _ _))
    (grid_mono (le_trans (le_max_left Mc Md) (le_max_right _ _)) hMc)
    (grid_mono (le_trans (le_max_right Mc Md) (le_max_right _ _)) hMd) (Nat.le_add_left _ _)⟩

theorem perRestrict_hlCond (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d) {N : ℕ}
    (hcN : c ∈ Grid 6 N) (hdN : d ∈ Grid 6 N) : HLCond (perRestrictPerm hf hc hd) := by
  obtain ⟨-, -, hfc⟩ := mem_gammaTwo.mp hf
  intro x hx
  obtain ⟨k, hkx, hxk⟩ := exists_gridPt_bracket_of_not_dyadic6 N hx
  rcases gridInterval_cases hcN hdN k with ⟨j, hj1, hj2⟩ | hfix
  · have hle := gridPt_six_le_succ N k
    have hin : ∀ y, gridPt 6 N k ≤ y → y ≤ gridPt 6 N (k + 1) → perRestrict f c d y = f y :=
      fun y hy1 hy2 => perRestrict_of_mem ⟨j, by linarith, by linarith⟩
    obtain ⟨a, b, i, i', hax, hxb, haff, hij⟩ := hfc x hx
    refine ⟨max a (gridPt 6 N k), min b (gridPt 6 N (k + 1)), i, i', max_lt hax hkx,
      lt_min hxb hxk, fun y hy1 hy2 => ?_, ?_⟩
    · have hy1' := le_trans (le_max_right _ _) hy1
      have hy2' := le_trans hy2 (min_le_right _ _)
      show perRestrict f c d y = perRestrict f c d (max a (gridPt 6 N k)) + _ * (y - _)
      rw [hin y hy1' hy2', hin _ (le_max_right _ _) (le_trans hy1 hy2')]
      exact haff.restrict (le_max_left _ _) (min_le_left _ _) y hy1 hy2
    · show i - i' = ⌊perRestrict f c d x⌋ - ⌊x⌋
      rw [hin x hkx.le hxk.le]
      exact hij
  · have hfix' : ∀ y, gridPt 6 N k ≤ y → y ≤ gridPt 6 N (k + 1) → perRestrict f c d y = y :=
      fun y hy1 hy2 => perRestrict_eq_self_of_boundary hf hc hd (hfix y hy1 hy2)
    refine ⟨gridPt 6 N k, gridPt 6 N (k + 1), 0, 0, hkx, hxk, fun y hy1 hy2 => ?_, ?_⟩
    · show perRestrict f c d y = perRestrict f c d (gridPt 6 N k) + _ * (y - _)
      rw [hfix' y hy1 hy2, hfix' _ le_rfl (le_trans hy1 hy2)]
      simp only [zpow_zero, one_mul]
      ring
    · show (0 : ℤ) - 0 = ⌊perRestrict f c d x⌋ - ⌊x⌋
      rw [hfix' x hkx.le hxk.le]
      simp

/-- **The restriction to `[c, d] + ℤ` is in `Γ₂`.** -/
theorem perRestrictPerm_mem_gammaTwo (hf : f ∈ gammaTwo) (hc : f c = c) (hd : f d = d)
    (hcG : ∃ M, c ∈ Grid 6 M) (hdG : ∃ M, d ∈ Grid 6 M) :
    perRestrictPerm hf hc hd ∈ gammaTwo := by
  obtain ⟨Mc, hMc⟩ := hcG
  obtain ⟨Md, hMd⟩ := hdG
  refine mem_gammaTwo.mpr ⟨(mem_PLGroup 6 slopes23).mpr ⟨perRestrict_strictMono hf hc hd,
    exists_perRestrict_gridAffine hf hc hd hMc hMd, ?_⟩,
    fun t => perRestrict_add_one (c := c) (d := d) hf t,
    perRestrict_hlCond hf hc hd (grid_mono (le_max_left Mc Md) hMc)
      (grid_mono (le_max_right Mc Md) hMd)⟩
  exact exists_perRestrict_gridAffine (gammaTwo.inv_mem hf) (perm_inv_apply_of_fix hc)
    (perm_inv_apply_of_fix hd) hMc hMd

end Restrict

/-- **Splitting at a fixed point.**  An element of `Υ_{Γ₂}([c, e])` fixing `c` and `d` is `f₁ f₂`
with `f₁ ∈ Υ_{Γ₂}([c, d])` agreeing with `f` on `[c, d]` and `f₂ ∈ Υ_{Γ₂}([d, e])`. -/
theorem exists_upsilon_split {f : Equiv.Perm ℚ} {c d e : ℚ} (hf : f ∈ gammaTwo)
    (hfs : SupportedIn f (perIoo c e)) (hc : f c = c) (hd : f d = d) (hcG : ∃ M, c ∈ Grid 6 M)
    (hdG : ∃ M, d ∈ Grid 6 M) :
    ∃ f₁ ∈ upsilon gammaTwo c d, ∃ f₂ ∈ upsilon gammaTwo d e, f = f₁ * f₂ ∧
      ∀ t, c ≤ t → t ≤ d → f₁ t = f t := by
  have hmem₁ := perRestrictPerm_mem_gammaTwo hf hc hd hcG hdG
  have hs₁ : SupportedIn (perRestrictPerm hf hc hd) (perIoo c d) := by
    intro t ht
    refine perRestrict_eq_self_of_boundary hf hc hd ?_
    rintro ⟨k, h1, h2⟩
    rcases lt_or_eq_of_le h1 with h1 | h1
    · rcases lt_or_eq_of_le h2 with h2 | h2
      · exact (ht ⟨k, h1, h2⟩).elim
      · exact Or.inr ⟨k, h2⟩
    · exact Or.inl ⟨k, h1.symm⟩
  have hs₂ : SupportedIn ((perRestrictPerm hf hc hd)⁻¹ * f) (perIoo d e) := by
    intro t ht
    show perRestrict f⁻¹ c d (f t) = t
    by_cases htI : t ∈ perIcc c d
    · rw [perRestrict_of_mem ((mem_perIcc_apply_iff hf hc hd).mpr htI), perm_inv_apply_self]
    · have hft : f t = t := by
        refine hfs t ?_
        rintro ⟨k, h1, h2⟩
        rcases le_or_gt (t + k) d with h | h
        · exact htI ⟨k, h1.le, h⟩
        · exact ht ⟨k, h, h2⟩
      rw [hft, perRestrict_of_not_mem htI]
  refine ⟨perRestrictPerm hf hc hd, mem_upsilon.mpr ⟨hmem₁, hs₁⟩,
    (perRestrictPerm hf hc hd)⁻¹ * f,
    mem_upsilon.mpr ⟨gammaTwo.mul_mem (gammaTwo.inv_mem hmem₁) hf, hs₂⟩,
    (mul_inv_cancel_left _ _).symm, fun t h1 h2 => ?_⟩
  have ht : t ∈ perIcc c d := ⟨0, by simpa using h1, by simpa using h2⟩
  show perRestrict f c d t = f t
  exact perRestrict_of_mem ht

#audit_axioms GroupApproximation.HydeLodha.gridInterval_cases
#audit_axioms GroupApproximation.HydeLodha.perRestrictPerm_mem_gammaTwo
#audit_axioms GroupApproximation.HydeLodha.exists_upsilon_split

end HydeLodha
end GroupApproximation
