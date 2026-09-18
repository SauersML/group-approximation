import GroupApproximation.Manuscript.NonMFNotes.Full.TWW.SubgroupRegularModels
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.BlockMatrix
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.Cosets

/-!
# Induced matrices from a normalizing element of finite order modulo a subgroup

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), finite-index half of the cyclic extension step
(Ozawa--Rørdam--Sato, GAFA 25 (2015), §3: induction from a finite-index
normal subgroup).

Let `π` be a regular-character model on a test set `F'`, let `k` normalize `H`,
and let `m > 0` be least with `k ^ m ∈ H`. The induced matrix of `x` has the
`(i, j)` block `π(cc k x i j)` when `cc k x i j ∈ H`, and `0` otherwise
(`inducedMat`). The block pattern is a permutation (`Cosets`). This file proves
the model estimates for the induced matrices: norm bound, approximate
multiplicativity, approximate star-compatibility and the trace formulas. Each
estimate only uses `π` at block coordinates lying in `H`, and those coordinates
are assumed to lie in `F'`.
-/

namespace GroupApproximation.Full.TWWCyclic

open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G]

variable {F' : Finset G} {ε : ℝ}

open scoped Classical in
/-- The model matrix of `g`, cut off to `0` outside `H`. -/
noncomputable def cutMat (H : Subgroup G)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) (g : G) :
    Matrix π.carrier π.carrier ℂ :=
  if g ∈ H then π.map g else 0

theorem cutMat_of_mem (H : Subgroup G)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {g : G}
    (hg : g ∈ H) : cutMat H π g = π.map g := by
  rw [cutMat, if_pos hg]

theorem cutMat_of_notMem (H : Subgroup G)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {g : G}
    (hg : g ∉ H) : cutMat H π g = 0 := by
  rw [cutMat, if_neg hg]

theorem norm_cutMat_le_one (H : Subgroup G)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {g : G}
    (hg : g ∈ H → g ∈ F') : ‖cutMat H π g‖ ≤ 1 := by
  by_cases h : g ∈ H
  · rw [cutMat_of_mem H π h]
    exact π.bounded g (hg h)
  · rw [cutMat_of_notMem H π h, norm_zero]
    exact zero_le_one

theorem norm_trace_cutMat_div_le (H : Subgroup G)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) (hε : 0 ≤ ε)
    {g : G} (hg : g ∈ H → g ∈ F') (hne : g ≠ 1) :
    ‖Matrix.trace (cutMat H π g) / (Fintype.card π.carrier : ℂ)‖ ≤ ε := by
  by_cases h : g ∈ H
  · rw [cutMat_of_mem H π h]
    exact π.trace_correct_ne g (hg h) hne
  · rw [cutMat_of_notMem H π h, Matrix.trace_zero, zero_div, norm_zero]
    exact hε

/-- The induced matrix of `x` on `Fin m × π.carrier`. -/
noncomputable def inducedMat (H : Subgroup G) (k : G) (m : ℕ)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) (x : G) :
    Matrix (Fin m × π.carrier) (Fin m × π.carrier) ℂ :=
  blockMat fun i j : Fin m => cutMat H π (cc k x i j)

/-! ## Norm bound -/

theorem norm_inducedMat_le_one {H : Subgroup G} {k : G} {m : ℕ}
    (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {x : G}
    (hxF : ∀ i j : Fin m, cc k x i j ∈ H → cc k x i j ∈ F') :
    ‖inducedMat H k m π x‖ ≤ 1 := by
  refine norm_blockMat_le (c := 1) (fun i j : Fin m => cutMat H π (cc k x i j))
    (fun i j : Fin m => cc k x i j ∈ H) zero_le_one
    (fun i j => norm_cutMat_le_one H π (hxF i j)) (fun i j hne => ?_)
    (fun i j j' hj hj' => Fin.ext (cc_row_unique hmin j.2 j'.2 hj hj'))
    (fun i i' j hi hi' => Fin.ext (cc_col_unique hmin i.2 i'.2 hi hi'))
  by_contra hn
  exact hne (cutMat_of_notMem H π hn)

/-- In every row the induced matrix of `x ∈ H ⊔ ⟨k⟩` has a used block. -/
theorem exists_row_mem {H : Subgroup G} {k : G} {m : ℕ} (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) (hm : 0 < m) (hkm : k ^ m ∈ H) {x : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers k) (i : Fin m) : ∃ l : Fin m, cc k x i l ∈ H := by
  obtain ⟨h, hh, r, hr, rfl⟩ := exists_mul_pow_lt hk hk' hm hkm hx
  obtain ⟨l, hl, hmem⟩ := cc_row_exists hk' hkm hh hr i.2
  exact ⟨⟨l, hl⟩, hmem⟩

/-! ## Approximate multiplicativity -/

theorem block_mul_sub_eq_zero (H : Subgroup G) (k : G) {m : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {x y : G}
    {i j : Fin m} (hn : cc k (x * y) i j ∉ H) :
    cutMat H π (cc k (x * y) i j) -
      ∑ l : Fin m, cutMat H π (cc k x i l) * cutMat H π (cc k y l j) = 0 := by
  rw [cutMat_of_notMem H π hn, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases ha : cc k x i l ∈ H
  · by_cases hb : cc k y l j ∈ H
    · have hab := H.mul_mem ha hb
      rw [cc_mul] at hab
      exact absurd hab hn
    · rw [cutMat_of_notMem H π hb, mul_zero]
  · rw [cutMat_of_notMem H π ha, zero_mul]

theorem norm_block_mul_sub_le {H : Subgroup G} {k : G} {m : ℕ}
    (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) (hm : 0 < m)
    (hkm : k ^ m ∈ H) (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {x y : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers k)
    (hxF : ∀ i j : Fin m, cc k x i j ∈ H → cc k x i j ∈ F')
    (hyF : ∀ i j : Fin m, cc k y i j ∈ H → cc k y i j ∈ F') (i j : Fin m)
    (hxy : cc k (x * y) i j ∈ H) :
    ‖cutMat H π (cc k (x * y) i j) -
      ∑ l : Fin m, cutMat H π (cc k x i l) * cutMat H π (cc k y l j)‖ ≤ ε := by
  obtain ⟨l₀, hl₀⟩ := exists_row_mem hk hk' hm hkm hx i
  have hb : cc k y l₀ j ∈ H := by
    have h := H.mul_mem (H.inv_mem hl₀) hxy
    rwa [cc_inv, cc_mul, inv_mul_cancel_left] at h
  have hzero : ∀ l ∈ (Finset.univ : Finset (Fin m)), l ≠ l₀ →
      cutMat H π (cc k x i l) * cutMat H π (cc k y l j) = 0 := by
    intro l _ hl
    have hn : cc k x i l ∉ H := fun h => hl (Fin.ext (cc_row_unique hmin l.2 l₀.2 h hl₀))
    rw [cutMat_of_notMem H π hn, zero_mul]
  rw [Finset.sum_eq_single l₀ hzero (fun hn => absurd (Finset.mem_univ l₀) hn),
    cutMat_of_mem H π hxy, cutMat_of_mem H π hl₀, cutMat_of_mem H π hb,
    ← cc_mul k x y i l₀ j]
  exact π.multiplicative _ (hxF i l₀ hl₀) _ (hyF l₀ j hb)

theorem norm_inducedMat_mul_sub_le {H : Subgroup G} {k : G} {m : ℕ}
    (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) (hm : 0 < m)
    (hkm : k ^ m ∈ H) (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {x y : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers k)
    (hxF : ∀ i j : Fin m, cc k x i j ∈ H → cc k x i j ∈ F')
    (hyF : ∀ i j : Fin m, cc k y i j ∈ H → cc k y i j ∈ F') (hε : 0 ≤ ε) :
    ‖inducedMat H k m π (x * y) - inducedMat H k m π x * inducedMat H k m π y‖ ≤ ε := by
  show ‖blockMat (fun i j : Fin m => cutMat H π (cc k (x * y) i j)) -
      blockMat (fun i j : Fin m => cutMat H π (cc k x i j)) *
        blockMat (fun i j : Fin m => cutMat H π (cc k y i j))‖ ≤ ε
  rw [blockMat_mul, blockMat_sub]
  refine norm_blockMat_le (c := ε)
    (fun i j : Fin m => cutMat H π (cc k (x * y) i j) -
      ∑ l : Fin m, cutMat H π (cc k x i l) * cutMat H π (cc k y l j))
    (fun i j : Fin m => cc k (x * y) i j ∈ H) hε (fun i j => ?_) (fun i j hne => ?_)
    (fun i j j' hj hj' => Fin.ext (cc_row_unique hmin j.2 j'.2 hj hj'))
    (fun i i' j hi hi' => Fin.ext (cc_col_unique hmin i.2 i'.2 hi hi'))
  · show ‖cutMat H π (cc k (x * y) i j) -
        ∑ l : Fin m, cutMat H π (cc k x i l) * cutMat H π (cc k y l j)‖ ≤ ε
    by_cases hxy : cc k (x * y) i j ∈ H
    · exact norm_block_mul_sub_le hk hk' hm hkm hmin π hx hxF hyF i j hxy
    · rw [block_mul_sub_eq_zero H k π hxy, norm_zero]
      exact hε
  · by_contra hn
    exact hne (block_mul_sub_eq_zero H k π hn)

/-! ## Approximate star-compatibility -/

theorem block_star_eq_zero (H : Subgroup G) (k : G)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {x : G}
    {i j : ℕ} (hn : cc k x j i ∉ H) :
    cutMat H π (cc k x⁻¹ i j) - (cutMat H π (cc k x j i))ᴴ = 0 := by
  have hn' : (cc k x j i)⁻¹ ∉ H := fun h => hn (inv_mem_iff.mp h)
  rw [← cc_inv, cutMat_of_notMem H π hn', cutMat_of_notMem H π hn,
    Matrix.conjTranspose_zero, sub_zero]

theorem norm_block_star_le (H : Subgroup G) (k : G)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {x : G}
    {i j : ℕ} (hmem : cc k x j i ∈ H) (hF : cc k x j i ∈ F') :
    ‖cutMat H π (cc k x⁻¹ i j) - (cutMat H π (cc k x j i))ᴴ‖ ≤ ε := by
  rw [← cc_inv, cutMat_of_mem H π (H.inv_mem hmem), cutMat_of_mem H π hmem]
  exact π.star_compatible _ hF

theorem norm_inducedMat_inv_sub_le {H : Subgroup G} {k : G} {m : ℕ}
    (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) {x : G}
    (hxF : ∀ i j : Fin m, cc k x i j ∈ H → cc k x i j ∈ F') (hε : 0 ≤ ε) :
    ‖inducedMat H k m π x⁻¹ - (inducedMat H k m π x)ᴴ‖ ≤ ε := by
  show ‖blockMat (fun i j : Fin m => cutMat H π (cc k x⁻¹ i j)) -
      (blockMat (fun i j : Fin m => cutMat H π (cc k x i j)))ᴴ‖ ≤ ε
  rw [blockMat_conjTranspose, blockMat_sub]
  refine norm_blockMat_le (c := ε)
    (fun i j : Fin m => cutMat H π (cc k x⁻¹ i j) - (cutMat H π (cc k x j i))ᴴ)
    (fun i j : Fin m => cc k x j i ∈ H) hε (fun i j => ?_) (fun i j hne => ?_)
    (fun i j j' hj hj' => Fin.ext (cc_col_unique hmin j.2 j'.2 hj hj'))
    (fun i i' j hi hi' => Fin.ext (cc_row_unique hmin i.2 i'.2 hi hi'))
  · show ‖cutMat H π (cc k x⁻¹ i j) - (cutMat H π (cc k x j i))ᴴ‖ ≤ ε
    by_cases hmem : cc k x j i ∈ H
    · exact norm_block_star_le H k π hmem (hxF j i hmem)
    · rw [block_star_eq_zero H k π hmem, norm_zero]
      exact hε
  · by_contra hn
    exact hne (block_star_eq_zero H k π hn)

/-! ## Traces -/

theorem card_induced {m : ℕ}
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) :
    Fintype.card (Fin m × π.carrier) = m * Fintype.card π.carrier := by
  rw [Fintype.card_prod, Fintype.card_fin]

theorem card_induced_pos {m : ℕ} (hm : 0 < m)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) :
    0 < Fintype.card (Fin m × π.carrier) := by
  rw [card_induced π]
  exact Nat.mul_pos hm π.nonempty

theorem trace_inducedMat (H : Subgroup G) (k : G) (m : ℕ)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) (x : G) :
    Matrix.trace (inducedMat H k m π x) =
      ∑ i : Fin m, Matrix.trace (cutMat H π (cc k x i i)) :=
  trace_blockMat (fun i j : Fin m => cutMat H π (cc k x i j))

theorem norm_trace_inducedMat_one_sub_le (H : Subgroup G) (k : G) {m : ℕ} (hm : 0 < m)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ))
    (h1 : (1 : G) ∈ F') :
    ‖Matrix.trace (inducedMat H k m π 1) / (Fintype.card (Fin m × π.carrier) : ℂ) - 1‖
      ≤ ε := by
  have hblock : ∀ i : Fin m,
      Matrix.trace (cutMat H π (cc k 1 i i)) = Matrix.trace (π.map 1) := by
    intro i
    rw [cc_one_self, cutMat_of_mem H π H.one_mem]
  have hsum : ∑ i : Fin m, Matrix.trace (cutMat H π (cc k 1 i i)) =
      (m : ℂ) * Matrix.trace (π.map 1) := by
    calc ∑ i : Fin m, Matrix.trace (cutMat H π (cc k 1 i i))
        = ∑ _i : Fin m, Matrix.trace (π.map 1) := Finset.sum_congr rfl fun i _ => hblock i
      _ = (m : ℂ) * Matrix.trace (π.map 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [trace_inducedMat, hsum, card_induced π, Nat.cast_mul, mul_div_mul_left _ _ hm0]
  exact π.trace_correct_one h1

theorem norm_trace_inducedMat_le (H : Subgroup G) (k : G) {m : ℕ} (hm : 0 < m)
    (π : MFTraceRecognition.RegularCharacterModel G F' ε fun _ : G => (1 : ℝ)) (hε : 0 ≤ ε)
    {x : G} (hxF : ∀ i j : Fin m, cc k x i j ∈ H → cc k x i j ∈ F') (hne : x ≠ 1) :
    ‖Matrix.trace (inducedMat H k m π x) / (Fintype.card (Fin m × π.carrier) : ℂ)‖ ≤ ε := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hdiv : Matrix.trace (inducedMat H k m π x) / (Fintype.card (Fin m × π.carrier) : ℂ) =
      (∑ i : Fin m, Matrix.trace (cutMat H π (cc k x i i)) /
        (Fintype.card π.carrier : ℂ)) / (m : ℂ) := by
    rw [trace_inducedMat, card_induced π, Nat.cast_mul, ← Finset.sum_div, div_div,
      mul_comm (m : ℂ)]
  rw [hdiv, norm_div, Complex.norm_natCast, div_le_iff₀ hm0]
  calc ‖∑ i : Fin m, Matrix.trace (cutMat H π (cc k x i i)) / (Fintype.card π.carrier : ℂ)‖
      ≤ ∑ i : Fin m,
          ‖Matrix.trace (cutMat H π (cc k x i i)) / (Fintype.card π.carrier : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, ε := Finset.sum_le_sum fun i _ =>
        norm_trace_cutMat_div_le H π hε (hxF i i) (cc_self_ne_one k hne i)
    _ = ε * m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

end GroupApproximation.Full.TWWCyclic
