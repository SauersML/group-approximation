import GroupApproximation.GroupTheory.HigmanThompson.CompactTrunc
import GroupApproximation.Meta.AxiomGuard

/-!
# `F_{n,∞}` conjugates into `F_{n,r}`

For `g ∈ geoF m`, the conjugate `compConjHom m r g` lies in the interval model
`compactF m r` (`compConj_mem_compactF`, for `r ≥ 1`).

* Every element of `F_{n,∞}` is eventually a translation by a multiple of `n - 1`
  (`geoF_translation`), because each generator is.
* Near `r` the conjugate is the affine contraction `t ↦ r - (r - t) n^{-k}`
  (`compConj_near`), through `compE_add_int_q`.
* On `(-∞, compE U₀]` the conjugate agrees with the conjugate by the finite truncation
  `compET J`, which is grid-affine by the composition lemma (`trunc_conj_gridAffine`);
  gluing it with the affine germ and the identity beyond `r` gives grid affinity everywhere
  (`compConj_gridAffine`).
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m r : ℕ)

/-! ## Eventual translations -/

theorem brownF_translation {g : Equiv.Perm ℚ} (hg : g ∈ brownF m) :
    ∃ T : ℕ, ∃ k : ℤ, ∀ t : ℚ, (T : ℚ) ≤ t → g t = t + k * ((m : ℚ) + 1) := by
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  obtain ⟨w, rfl⟩ := hg
  induction w using PresentedGroup.induction_on with
  | H z =>
    induction z using FreeGroup.induction_on with
    | C1 => exact ⟨0, 0, fun t _ => by simp⟩
    | of x =>
        refine ⟨x.val + 1, 1, fun t ht => ?_⟩
        rw [brownX_of_fin, brownEval_X, xg_apply, xfun_of_ge (by push_cast at ht; linarith)]
        ring
    | inv_of x ih =>
        obtain ⟨T, k, hT⟩ := ih
        refine ⟨T + k.natAbs * (m + 1), -k, fun t ht => ?_⟩
        have hab : (k : ℚ) ≤ (k.natAbs : ℚ) := by
          have h2 := (Int.cast_le (R := ℚ)).mpr (Int.le_natAbs (a := k))
          rw [Int.cast_natCast] at h2
          exact h2
        have hmul : (k : ℚ) * ((m : ℚ) + 1) ≤ (k.natAbs : ℚ) * ((m : ℚ) + 1) :=
          mul_le_mul_of_nonneg_right hab hq.le
        push_cast at ht
        simp only [map_inv]
        rw [Equiv.Perm.inv_eq_iff_eq, hT _ (by push_cast; linarith)]
        push_cast
        ring
    | mul x y ihx ihy =>
        obtain ⟨Tx, kx, hTx⟩ := ihx
        obtain ⟨Ty, ky, hTy⟩ := ihy
        refine ⟨Ty + Tx + ky.natAbs * (m + 1), kx + ky, fun t ht => ?_⟩
        have hab : (-(ky : ℚ)) ≤ (ky.natAbs : ℚ) := by
          have h : -ky ≤ (ky.natAbs : ℤ) := by
            have h1 := Int.le_natAbs (a := -ky)
            rwa [Int.natAbs_neg] at h1
          have h2 := (Int.cast_le (R := ℚ)).mpr h
          rw [Int.cast_neg, Int.cast_natCast] at h2
          exact h2
        have hmul : (-(ky : ℚ)) * ((m : ℚ) + 1) ≤ (ky.natAbs : ℚ) * ((m : ℚ) + 1) :=
          mul_le_mul_of_nonneg_right hab hq.le
        have hnat : (0 : ℚ) ≤ (ky.natAbs : ℚ) * ((m : ℚ) + 1) := by positivity
        push_cast at ht
        have h0 : (0 : ℚ) ≤ Tx := Nat.cast_nonneg Tx
        have h0' : (0 : ℚ) ≤ Ty := Nat.cast_nonneg Ty
        simp only [map_mul, Equiv.Perm.mul_apply]
        rw [hTy t (by linarith), hTx _ (by linarith)]
        push_cast
        ring

theorem geoF_translation {g : Equiv.Perm ℚ} (hg : g ∈ geoF m) :
    ∃ T : ℕ, ∃ k : ℤ, ∀ t : ℚ, (T : ℚ) ≤ t → g t = t + k * ((m : ℚ) + 1) := by
  rw [geoF_eq_brownF] at hg
  exact brownF_translation m hg

/-! ## Conjugation facts -/

theorem compE_add_int_q (k : ℤ) {u : ℚ} (hu : (r : ℚ) - 1 ≤ u)
    (hu' : (r : ℚ) - 1 ≤ u + k * ((m : ℚ) + 1)) :
    compE m r (u + k * ((m : ℚ) + 1)) =
      (r : ℚ) - ((r : ℚ) - compE m r u) * ((m : ℚ) + 2) ^ (-k) := by
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have h := compE_add_nat_q m r k' hu
    push_cast at h ⊢
    rw [h, zpow_neg, zpow_natCast]
    field_simp
  · obtain ⟨k', hk'⟩ := Int.exists_eq_neg_ofNat hk.le
    subst hk'
    have h := compE_add_nat_q m r k' hu'
    have e : u + ((-(k' : ℤ) : ℤ) : ℚ) * ((m : ℚ) + 1) + (k' : ℚ) * ((m : ℚ) + 1) = u := by
      push_cast
      ring
    rw [e] at h
    rw [neg_neg, zpow_natCast]
    have hpk : (0 : ℚ) < ((m : ℚ) + 2) ^ k' := pow_pos hp k'
    field_simp at h
    linear_combination (-1 : ℚ) * h

theorem compConj_strictMono {g : Equiv.Perm ℚ} (hg : StrictMono g) :
    StrictMono (compConjHom m r g) := by
  intro t t' htt'
  simp only [compConjHom_apply]
  by_cases h' : t' < r
  · have ht : t < r := lt_trans htt' h'
    rw [compConjFun_of_lt m r g ht, compConjFun_of_lt m r g h']
    exact compE_strictMono m r (hg (compEinv_strictMonoOn m r ht h' htt'))
  · rw [compConjFun_of_ge m r g (not_lt.mp h')]
    by_cases ht : t < r
    · exact lt_of_lt_of_le (compConjFun_lt m r g ht) (not_lt.mp h')
    · rw [compConjFun_of_ge m r g (not_lt.mp ht)]
      exact htt'

theorem compConj_fix_nonpos (hr : 1 ≤ r) {g : Equiv.Perm ℚ} (hg0 : ∀ t : ℚ, t ≤ 0 → g t = t)
    {t : ℚ} (ht : t ≤ 0) : compConjHom m r g t = t := by
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have ht1 : t ≤ (r : ℚ) - 1 := by linarith
  rw [compConjHom_apply, compConjFun_of_lt m r g (by linarith), compEinv_of_le m r ht1,
    hg0 t ht, compE_of_le m r ht1]

/-- **The germ at `r`.** -/
theorem compConj_near (hr : 1 ≤ r) {g : Equiv.Perm ℚ} {T : ℕ} {k : ℤ}
    (hT : ∀ t : ℚ, (T : ℚ) ≤ t → g t = t + k * ((m : ℚ) + 1)) {t : ℚ}
    (ht1 : compE m r ((r : ℚ) - 1 + ((T + k.natAbs * (m + 1) : ℕ) : ℚ)) ≤ t) (ht2 : t < r) :
    compConjHom m r g t = (r : ℚ) - ((r : ℚ) - t) * ((m : ℚ) + 2) ^ (-k) := by
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hu : (r : ℚ) - 1 + ((T + k.natAbs * (m + 1) : ℕ) : ℚ) ≤ compEinv m r t := by
    by_contra h
    have h' := compE_strictMono m r (not_le.mp h)
    rw [compE_compEinv m r ht2] at h'
    linarith
  have hab : (-(k : ℚ)) ≤ (k.natAbs : ℚ) := by
    have h : -k ≤ (k.natAbs : ℤ) := by
      have h1 := Int.le_natAbs (a := -k)
      rwa [Int.natAbs_neg] at h1
    have h2 := (Int.cast_le (R := ℚ)).mpr h
    rw [Int.cast_neg, Int.cast_natCast] at h2
    exact h2
  have hmul : (-(k : ℚ)) * ((m : ℚ) + 1) ≤ (k.natAbs : ℚ) * ((m : ℚ) + 1) :=
    mul_le_mul_of_nonneg_right hab hq.le
  have hnat : (0 : ℚ) ≤ (k.natAbs : ℚ) * ((m : ℚ) + 1) := by positivity
  have h0T : (0 : ℚ) ≤ T := Nat.cast_nonneg T
  push_cast at hu
  rw [compConjHom_apply, compConjFun_of_lt m r g ht2, hT _ (by linarith),
    compE_add_int_q m r k (by linarith) (by linarith), compE_compEinv m r ht2]

/-! ## Grid affinity of the conjugate -/

theorem compEinvT_strictMono (J : ℕ) : StrictMono (compEinvT m r J) := by
  intro s t hst
  by_contra h
  have h' := (compET_strictMono m r J).monotone (not_lt.mp h)
  rw [compET_compEinvT, compET_compEinvT] at h'
  exact absurd hst (not_lt.mpr h')

/-- The conjugate of a grid-affine permutation by a truncation is grid-affine. -/
theorem trunc_conj_gridAffine (J : ℕ) {g : Equiv.Perm ℚ} (hgm : StrictMono g)
    {Ng Bg Ngi Bgi : ℕ} (hgA : GridAffine (m + 2) (powSlopes m) g Ng Bg)
    (hgiA : GridAffine (m + 2) (powSlopes m) ⇑g⁻¹ Ngi Bgi) :
    ∃ N B : ℕ, GridAffine (m + 2) (powSlopes m) (compET m r J ∘ g ∘ compEinvT m r J) N B := by
  have h1 := (compEinvT_gridAffine m r J).comp (compET_gridAffine m r J) hgA
    (compEinvT_strictMono m r J) (compEinvT_compET m r J)
  have h3 := hgiA.comp hgA (compET_gridAffine m r J) (strictMono_perm_inv hgm)
    (fun y => perm_inv_apply_self g y)
  have hinner : StrictMono (⇑g ∘ compEinvT m r J) := hgm.comp (compEinvT_strictMono m r J)
  have hright : ∀ y, (⇑g ∘ compEinvT m r J) ((compET m r J ∘ ⇑g⁻¹) y) = y := by
    intro y
    simp only [Function.comp_apply, compEinvT_compET, perm_apply_inv_self]
  exact ⟨_, _, h1.comp h3 (compET_gridAffine m r J) hinner hright⟩

theorem natPow_zpow_mem_grid (k : ℤ) : ((m : ℚ) + 2) ^ (-k) ∈ Grid (m + 2) k.natAbs := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_neg, zpow_natCast]
    exact inv_pow_mem_grid m (by simp)
  · obtain ⟨k', hk'⟩ := Int.exists_eq_neg_ofNat hk.le
    subst hk'
    rw [neg_neg, zpow_natCast]
    have e : ((m : ℚ) + 2) ^ k' = ((((m : ℤ) + 2) ^ k' : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    exact int_mem_grid _ _

theorem compConj_gridAffine (hr : 1 ≤ r) {g : Equiv.Perm ℚ} (hg : g ∈ geoF m) :
    ∃ N B : ℕ, GridAffine (m + 2) (powSlopes m) ⇑(compConjHom m r g) N B := by
  obtain ⟨T, k, hT⟩ := geoF_translation m hg
  obtain ⟨⟨hgm, ⟨Ng, Bg, hgA⟩, ⟨Ngi, Bgi, hgiA⟩⟩, -, -⟩ := hg
  have hq : (0 : ℚ) < (m : ℚ) + 1 := mOne_pos m
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  obtain ⟨NA, BA, hA⟩ := trunc_conj_gridAffine m r (T + k.natAbs * (m + 1) + k.natAbs * (m + 1))
    hgm hgA hgiA
  -- the affine germ at `r`, glued with the identity beyond `r`
  set s : ℚ := ((m : ℚ) + 2) ^ (-k) with hs
  have hsΩ : s ∈ powSlopes m := ⟨-k, rfl⟩
  have hsB : s ∈ Grid (m + 2) (k.natAbs + k.natAbs) :=
    grid_mono (by omega) (natPow_zpow_mem_grid m k)
  have hbB : (r : ℚ) * (1 - s) ∈ Grid (m + 2) (k.natAbs + k.natAbs) := by
    have hr_mem : (r : ℚ) ∈ Grid (m + 2) k.natAbs := by
      simpa using int_mem_grid (m := m + 2) k.natAbs (r : ℤ)
    have h1mem : (1 : ℚ) ∈ Grid (m + 2) k.natAbs := by
      simpa using int_mem_grid (m := m + 2) k.natAbs 1
    exact grid_mul hr_mem (grid_sub h1mem (natPow_zpow_mem_grid m k))
  have hB := gridAffine_affine (m := m + 2) (Ω := powSlopes m) hsΩ hsB hbB
  have hId : GridAffine (m + 2) (powSlopes m) id 0 (k.natAbs + k.natAbs) :=
    (gridAffine_id (m := m + 2) (Ω := powSlopes m)).mono_bound (Nat.zero_le _)
  set F₂ : ℚ → ℚ := fun t => if t ≤ r then s * t + (r : ℚ) * (1 - s) else t with hF₂
  have hF₂A : GridAffine (m + 2) (powSlopes m) F₂ 0 (k.natAbs + k.natAbs) := by
    refine GridAffine.glue hB hId (p := (r : ℚ)) (by simpa using int_mem_grid (m := m + 2) 0 (r : ℤ))
      (fun t ht => ?_) (fun t ht => ?_)
    · simp only [hF₂, if_pos ht]
    · by_cases h : t ≤ r
      · have htr : t = r := le_antisymm h ht
        subst htr
        show (if (r : ℚ) ≤ r then s * r + (r : ℚ) * (1 - s) else (r : ℚ)) = (r : ℚ)
        rw [if_pos le_rfl]
        ring
      · simp only [hF₂, if_neg h, id]
  -- common level
  set L : ℕ := NA + ((T + k.natAbs * (m + 1)) / (m + 1) + 1) with hL
  have hNAL : NA ≤ L := by
    rw [hL]
    exact Nat.le_add_right _ _
  have hA' := (hA.mono_level hNAL).mono_bound
    (show BA + L ≤ BA + (k.natAbs + k.natAbs) + L by omega)
  have hF' := (hF₂A.mono_level (Nat.zero_le L)).mono_bound
    (show k.natAbs + k.natAbs + L ≤ BA + (k.natAbs + k.natAbs) + L by omega)
  have hblk : (T + k.natAbs * (m + 1)) / (m + 1) + 1 ≤ L := by
    rw [hL]
    exact Nat.le_add_left _ _
  have hp₀ : compE m r ((r : ℚ) - 1 + ((T + k.natAbs * (m + 1) : ℕ) : ℚ)) ∈ Grid (m + 2) L :=
    grid_mono hblk (compE_block_mem m r (T + k.natAbs * (m + 1)))
  refine ⟨L, BA + (k.natAbs + k.natAbs) + L, GridAffine.glue hA' hF' hp₀ (fun t ht => ?_)
    (fun t ht => ?_)⟩
  · -- below the germ: the truncated conjugate
    have htr : t < r := lt_of_le_of_lt ht (compE_lt m r _)
    have hJle : compE m r ((r : ℚ) - 1 + ((T + k.natAbs * (m + 1) : ℕ) : ℚ)) ≤
        compE m r ((r : ℚ) - 1 + ((T + k.natAbs * (m + 1) + k.natAbs * (m + 1) : ℕ) : ℚ)) := by
      apply (compE_strictMono m r).monotone
      push_cast
      have : (0 : ℚ) ≤ (k.natAbs : ℚ) * ((m : ℚ) + 1) := by positivity
      linarith
    have hinvT : compEinvT m r (T + k.natAbs * (m + 1) + k.natAbs * (m + 1)) t = compEinv m r t := by
      simp only [compEinvT, if_pos (le_trans ht hJle)]
    have hu : compEinv m r t ≤ (r : ℚ) - 1 + ((T + k.natAbs * (m + 1) : ℕ) : ℚ) := by
      by_contra h
      have h' := compE_strictMono m r (not_le.mp h)
      rw [compE_compEinv m r htr] at h'
      linarith
    have hgu : g (compEinv m r t) ≤
        (r : ℚ) - 1 + ((T + k.natAbs * (m + 1) + k.natAbs * (m + 1) : ℕ) : ℚ) := by
      have h1 := hgm.monotone hu
      have hTle : (T : ℚ) ≤ (r : ℚ) - 1 + ((T + k.natAbs * (m + 1) : ℕ) : ℚ) := by
        push_cast
        have : (0 : ℚ) ≤ (k.natAbs : ℚ) * ((m : ℚ) + 1) := by positivity
        linarith
      rw [hT _ hTle] at h1
      have hab : (k : ℚ) ≤ (k.natAbs : ℚ) := by
        have h2 := (Int.cast_le (R := ℚ)).mpr (Int.le_natAbs (a := k))
        rw [Int.cast_natCast] at h2
        exact h2
      have hmul : (k : ℚ) * ((m : ℚ) + 1) ≤ (k.natAbs : ℚ) * ((m : ℚ) + 1) :=
        mul_le_mul_of_nonneg_right hab hq.le
      push_cast at h1 ⊢
      linarith
    show compConjFun m r g t = compET m r _ (g (compEinvT m r _ t))
    rw [compConjFun_of_lt m r g htr, hinvT, compET_of_le m r hgu]
  · -- at and beyond the germ
    by_cases htr : t < r
    · rw [compConj_near m r hr hT ht htr]
      simp only [hF₂, if_pos htr.le]
      ring
    · have htr' : (r : ℚ) ≤ t := not_lt.mp htr
      rw [compConjHom_apply, compConjFun_of_ge m r g htr']
      by_cases h : t ≤ r
      · have ht' : t = r := le_antisymm h htr'
        subst ht'
        show (r : ℚ) = (if (r : ℚ) ≤ r then s * r + (r : ℚ) * (1 - s) else (r : ℚ))
        rw [if_pos le_rfl]
        ring
      · simp only [hF₂, if_neg h]

/-- **Conjugates of `F_{n,∞}` lie in `F_{n,r}`.** -/
theorem compConj_mem_compactF (hr : 1 ≤ r) {g : Equiv.Perm ℚ} (hg : g ∈ geoF m) :
    compConjHom m r g ∈ compactF m r := by
  obtain ⟨N, B, hA⟩ := compConj_gridAffine m r hr hg
  obtain ⟨Ni, Bi, hAi⟩ := compConj_gridAffine m r hr ((geoF m).inv_mem hg)
  obtain ⟨⟨hgm, -, -⟩, hg0, -⟩ := hg
  rw [map_inv] at hAi
  refine ⟨⟨compConj_strictMono m r hgm, ⟨N, B, hA⟩, ⟨Ni, Bi, hAi⟩⟩,
    fun t ht => compConj_fix_nonpos m r hr hg0 ht, fun t ht => ?_⟩
  rw [compConjHom_apply, compConjFun_of_ge m r g ht]

theorem map_compConj_le_compactF (hr : 1 ≤ r) : (geoF m).map (compConjHom m r) ≤ compactF m r := by
  rintro _ ⟨g, hg, rfl⟩
  exact compConj_mem_compactF m r hr hg

#audit_axioms GroupApproximation.HigmanThompson.geoF_translation
#audit_axioms GroupApproximation.HigmanThompson.compConj_near
#audit_axioms GroupApproximation.HigmanThompson.map_compConj_le_compactF

end HigmanThompson
end GroupApproximation
