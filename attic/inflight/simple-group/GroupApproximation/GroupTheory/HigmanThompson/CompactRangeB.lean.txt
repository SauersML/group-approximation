import GroupApproximation.GroupTheory.HigmanThompson.CompactRangeA
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's isomorphism `F_{n,r} ≅ F_{n,∞}`

`compactF m r ≤ (geoF m).map (compConjHom m r)` (`compactF_le_map`), for `r ≥ 1`.  Given
`f ∈ F_{n,r}`, its germ at `r` is `t ↦ r - (r - t) n^k` (`compactF_germ`); multiplying by the
conjugate of `x_0^k`, whose germ is the inverse contraction, gives an element `h` fixing a
neighbourhood of `r`.  Such an `h` conjugates back into `F_{n,∞}` (`compConjInv_mem_geoF`):
below a block point the back-conjugate agrees with the conjugate by a finite truncation,
and beyond it is the identity.

Together with `map_compConj_le_compactF`, conjugation is an isomorphism
`geoF m ≃* compactF m r` (`geoFEquivCompactF`), so `F_{n,r}` is finitely presented
(`compactF_isFinitelyPresented`).
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m r : ℕ)

/-! ## Powers of `x_0` -/

theorem xg_zero_pow_translation (j : ℕ) : ∀ t : ℚ, (((j + 1) * (m + 2) : ℕ) : ℚ) ≤ t →
    (xg m 0 ^ j) t = t + j * ((m : ℚ) + 1) := by
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  induction j with
  | zero => exact fun t _ => by simp
  | succ j ih =>
    intro t ht
    have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    push_cast at ht
    rw [pow_succ, Equiv.Perm.mul_apply, xg_apply, xfun_of_ge (by push_cast; nlinarith),
      ih _ (by push_cast; nlinarith)]
    push_cast
    ring

theorem xg_zero_inv_pow_translation (j : ℕ) : ∀ t : ℚ, (((j + 1) * (m + 2) : ℕ) : ℚ) ≤ t →
    ((xg m 0)⁻¹ ^ j) t = t - j * ((m : ℚ) + 1) := by
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  induction j with
  | zero => exact fun t _ => by simp
  | succ j ih =>
    intro t ht
    have hj0 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    push_cast at ht
    rw [pow_succ, Equiv.Perm.mul_apply, xg_inv_of_ge m (by push_cast; nlinarith),
      ih _ (by push_cast; nlinarith)]
    push_cast
    ring

theorem xg_zero_zpow_translation (j : ℤ) : ∀ t : ℚ, (((j.natAbs + 1) * (m + 2) : ℕ) : ℚ) ≤ t →
    (xg m 0 ^ j) t = t + j * ((m : ℚ) + 1) := by
  intro t ht
  rcases le_or_gt 0 j with hj | hj
  · obtain ⟨j', rfl⟩ := Int.eq_ofNat_of_zero_le hj
    rw [zpow_natCast, xg_zero_pow_translation m j' t (by simpa using ht)]
    simp
  · obtain ⟨j', hj'⟩ := Int.exists_eq_neg_ofNat hj.le
    subst hj'
    rw [zpow_neg, zpow_natCast, ← inv_pow, xg_zero_inv_pow_translation m j' t (by simpa using ht)]
    push_cast
    ring

/-! ## Germs at `r` -/

theorem compactF_lt {h : Equiv.Perm ℚ} (hh : h ∈ compactF m r) {t : ℚ} (ht : t < r) : h t < r := by
  obtain ⟨⟨hm, -, -⟩, -, hfr⟩ := hh
  have h1 := hm ht
  rwa [hfr r le_rfl] at h1

theorem compactF_germ {f : Equiv.Perm ℚ} (hf : f ∈ compactF m r) :
    ∃ t₀ : ℚ, t₀ < r ∧ ∃ k : ℤ, ∀ t : ℚ, t₀ ≤ t → t ≤ r →
      f t = (r : ℚ) - ((r : ℚ) - t) * ((m : ℚ) + 2) ^ k := by
  obtain ⟨⟨-, ⟨N, B, hA⟩, -⟩, -, hfr⟩ := hf
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hcastn : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  obtain ⟨s, ⟨kk, rfl⟩, -, haff⟩ := hA.slope ((r : ℤ) * ((m : ℤ) + 2) ^ N - 1)
  have hpN : (0 : ℚ) < ((m : ℚ) + 2) ^ N := pow_pos hp N
  have hgp1 : gridPt (m + 2) N ((r : ℤ) * ((m : ℤ) + 2) ^ N - 1 + 1) = r := by
    have e : (((r : ℤ) * ((m : ℤ) + 2) ^ N - 1 + 1 : ℤ) : ℚ) = (r : ℚ) * ((m : ℚ) + 2) ^ N := by
      push_cast
      ring
    rw [gridPt, hcastn, e, mul_div_assoc, div_self hpN.ne', mul_one]
  have hgp0 : gridPt (m + 2) N ((r : ℤ) * ((m : ℤ) + 2) ^ N - 1) =
      (r : ℚ) - (((m : ℚ) + 2) ^ N)⁻¹ := by
    have e : (((r : ℤ) * ((m : ℤ) + 2) ^ N - 1 : ℤ) : ℚ) = (r : ℚ) * ((m : ℚ) + 2) ^ N - 1 := by
      push_cast
      ring
    rw [gridPt, hcastn, e, sub_div, mul_div_assoc, div_self hpN.ne', mul_one, one_div]
  have hinvpos : 0 < (((m : ℚ) + 2) ^ N)⁻¹ := inv_pos.mpr hpN
  refine ⟨(r : ℚ) - (((m : ℚ) + 2) ^ N)⁻¹, by linarith, kk, fun t ht1 ht2 => ?_⟩
  have h1 := haff t (by rw [hgp0]; exact ht1) (by rw [hgp1]; exact ht2)
  have h2 := haff r (by rw [hgp0]; linarith) (by rw [hgp1])
  rw [hfr r le_rfl] at h2
  rw [h1]
  linear_combination (-1 : ℚ) * h2

/-! ## Conjugating back -/

/-- The back-conjugate of `h`, as a function. -/
noncomputable def compConjInvFun (h : Equiv.Perm ℚ) (u : ℚ) : ℚ := compEinv m r (h (compE m r u))

/-- The back-conjugate of an element of `F_{n,r}`, as a permutation. -/
noncomputable def compConjInv {h : Equiv.Perm ℚ} (hh : h ∈ compactF m r) : Equiv.Perm ℚ where
  toFun := compConjInvFun m r h
  invFun := compConjInvFun m r h⁻¹
  left_inv u := by
    simp only [compConjInvFun]
    rw [compE_compEinv m r (compactF_lt m r hh (compE_lt m r u)), perm_inv_apply_self,
      compEinv_compE]
  right_inv u := by
    simp only [compConjInvFun]
    rw [compE_compEinv m r (compactF_lt m r ((compactF m r).inv_mem hh) (compE_lt m r u)),
      perm_apply_inv_self, compEinv_compE]

theorem compConj_compConjInv {h : Equiv.Perm ℚ} (hh : h ∈ compactF m r) :
    compConjHom m r (compConjInv m r hh) = h := by
  ext t
  rw [compConjHom_apply]
  by_cases ht : t < r
  · rw [compConjFun_of_lt m r _ ht]
    show compE m r (compEinv m r (h (compE m r (compEinv m r t)))) = h t
    rw [compE_compEinv m r ht, compE_compEinv m r (compactF_lt m r hh ht)]
  · have ht' : (r : ℚ) ≤ t := not_lt.mp ht
    rw [compConjFun_of_ge m r _ ht']
    obtain ⟨-, -, hfr⟩ := hh
    exact (hfr t ht').symm

theorem compConjInvFun_gridAffine {h : Equiv.Perm ℚ} (hh : h ∈ compactF m r) (J : ℕ)
    (hfix : ∀ t : ℚ, compE m r ((r : ℚ) - 1 + J) ≤ t → h t = t) :
    ∃ N B : ℕ, GridAffine (m + 2) (powSlopes m) (compConjInvFun m r h) N B := by
  obtain ⟨⟨hhm, ⟨Nh, Bh, hA⟩, ⟨Nhi, Bhi, hAi⟩⟩, -, -⟩ := hh
  have h1 := (compET_gridAffine m r J).comp (compEinvT_gridAffine m r J) hA
    (compET_strictMono m r J) (compET_compEinvT m r J)
  have h3 := hAi.comp hA (compEinvT_gridAffine m r J) (strictMono_perm_inv hhm)
    (fun y => perm_inv_apply_self h y)
  have hinner : StrictMono (⇑h ∘ compET m r J) := hhm.comp (compET_strictMono m r J)
  have hright : ∀ y, (⇑h ∘ compET m r J) ((compEinvT m r J ∘ ⇑h⁻¹) y) = y := by
    intro y
    simp only [Function.comp_apply, compET_compEinvT, perm_apply_inv_self]
  obtain ⟨NA, BA, hAA⟩ : ∃ N B : ℕ,
      GridAffine (m + 2) (powSlopes m) (compEinvT m r J ∘ h ∘ compET m r J) N B :=
    ⟨_, _, h1.comp h3 (compEinvT_gridAffine m r J) hinner hright⟩
  have hId : GridAffine (m + 2) (powSlopes m) id NA (BA + NA) :=
    ((gridAffine_id (m := m + 2) (Ω := powSlopes m)).mono_level (Nat.zero_le NA)).mono_bound
      (by omega)
  have hAA' := hAA.mono_bound (show BA ≤ BA + NA by omega)
  have hU : (r : ℚ) - 1 + J ∈ Grid (m + 2) NA := by
    have e : (r : ℚ) - 1 + J = (((r : ℤ) - 1 + J : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    exact int_mem_grid _ _
  refine ⟨NA, BA + NA, GridAffine.glue hAA' hId hU (fun u hu => ?_) (fun u hu => ?_)⟩
  · have hle : h (compE m r u) ≤ compE m r ((r : ℚ) - 1 + J) := by
      have h2 := hhm.monotone ((compE_strictMono m r).monotone hu)
      rwa [hfix _ le_rfl] at h2
    show compEinv m r (h (compE m r u)) = compEinvT m r J (h (compET m r J u))
    rw [compET_of_le m r hu]
    simp only [compEinvT, if_pos hle]
  · show compEinv m r (h (compE m r u)) = u
    rw [hfix _ ((compE_strictMono m r).monotone hu), compEinv_compE]

theorem compConjInv_mem_geoF (hr : 1 ≤ r) {h : Equiv.Perm ℚ} (hh : h ∈ compactF m r) (J : ℕ)
    (hfix : ∀ t : ℚ, compE m r ((r : ℚ) - 1 + J) ≤ t → h t = t) :
    compConjInv m r hh ∈ geoF m := by
  have hhinv := (compactF m r).inv_mem hh
  have hfix' : ∀ t : ℚ, compE m r ((r : ℚ) - 1 + J) ≤ t → h⁻¹ t = t := by
    intro t ht
    rw [Equiv.Perm.inv_eq_iff_eq, hfix t ht]
  obtain ⟨N, B, hA⟩ := compConjInvFun_gridAffine m r hh J hfix
  obtain ⟨Ni, Bi, hAi⟩ := compConjInvFun_gridAffine m r hhinv J hfix'
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hparts := hh
  obtain ⟨⟨hhm, -, -⟩, hh0, -⟩ := hparts
  refine ⟨⟨fun u u' huu' => ?_, ⟨N, B, hA⟩, ⟨Ni, Bi, hAi⟩⟩, fun u hu => ?_, r + J, 0,
    fun u hu => ?_⟩
  · show compEinv m r (h (compE m r u)) < compEinv m r (h (compE m r u'))
    exact compEinv_strictMonoOn m r (compactF_lt m r hh (compE_lt m r u))
      (compactF_lt m r hh (compE_lt m r u')) (hhm (compE_strictMono m r huu'))
  · have hu1 : u ≤ (r : ℚ) - 1 := by linarith
    show compEinv m r (h (compE m r u)) = u
    rw [compE_of_le m r hu1, hh0 u hu, compEinv_of_le m r hu1]
  · have hu1 : (r : ℚ) - 1 + J ≤ u := by push_cast at hu; linarith
    show compEinv m r (h (compE m r u)) = u + ((0 : ℤ) : ℚ)
    rw [hfix _ ((compE_strictMono m r).monotone hu1), compEinv_compE]
    simp

/-! ## The isomorphism -/

theorem compactF_le_map (hr : 1 ≤ r) : compactF m r ≤ (geoF m).map (compConjHom m r) := by
  intro f hf
  have hp : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  obtain ⟨t₀, ht₀, k, hk⟩ := compactF_germ m r hf
  have hz : xg m 0 ^ k ∈ geoF m := zpow_mem (xg_mem_geoF m 0) k
  have hzC : ∀ t : ℚ,
      compE m r ((r : ℚ) - 1 + (((k.natAbs + 1) * (m + 2) + k.natAbs * (m + 1) : ℕ) : ℚ)) ≤ t →
      t < r → compConjHom m r (xg m 0 ^ k) t = (r : ℚ) - ((r : ℚ) - t) * ((m : ℚ) + 2) ^ (-k) :=
    fun t h1 h2 => compConj_near m r hr (xg_zero_zpow_translation m k) h1 h2
  set t₁ := compE m r ((r : ℚ) - 1 + (((k.natAbs + 1) * (m + 2) + k.natAbs * (m + 1) : ℕ) : ℚ))
    with ht₁
  have ht₁r : t₁ < r := compE_lt m r _
  have hpk : ((m : ℚ) + 2) ^ k * ((m : ℚ) + 2) ^ (-k) = 1 := by
    rw [← zpow_add₀ hp.ne', add_neg_cancel, zpow_zero]
  have hpk' : ((m : ℚ) + 2) ^ (-k) * ((m : ℚ) + 2) ^ k = 1 := by
    rw [← zpow_add₀ hp.ne', neg_add_cancel, zpow_zero]
  have hmem : compConjHom m r (xg m 0 ^ k) * f ∈ compactF m r :=
    (compactF m r).mul_mem (compConj_mem_compactF m r hr hz) hf
  set t₂ := max t₀ ((r : ℚ) - ((r : ℚ) - t₁) * ((m : ℚ) + 2) ^ (-k)) with ht₂def
  have ht₂ : t₂ < r := by
    refine max_lt ht₀ ?_
    have h1 := mul_pos (sub_pos.mpr ht₁r) (zpow_pos hp (-k))
    linarith
  have hfixh : ∀ t : ℚ, t₂ ≤ t → (compConjHom m r (xg m 0 ^ k) * f) t = t := by
    intro t ht
    rw [Equiv.Perm.mul_apply]
    by_cases htr : t < r
    · have hft := hk t (le_trans (le_max_left _ _) ht) htr.le
      have h1 : (r : ℚ) - t ≤ ((r : ℚ) - t₁) * ((m : ℚ) + 2) ^ (-k) := by
        linarith [le_trans (le_max_right _ _) ht]
      have h2 : ((r : ℚ) - t) * ((m : ℚ) + 2) ^ k ≤
          ((r : ℚ) - t₁) * ((m : ℚ) + 2) ^ (-k) * ((m : ℚ) + 2) ^ k :=
        mul_le_mul_of_nonneg_right h1 (zpow_pos hp k).le
      have h3 : ((r : ℚ) - t₁) * ((m : ℚ) + 2) ^ (-k) * ((m : ℚ) + 2) ^ k = (r : ℚ) - t₁ := by
        rw [mul_assoc, hpk', mul_one]
      have hft1 : t₁ ≤ f t := by
        rw [hft]
        linarith
      have hft2 : f t < r := by
        rw [hft]
        have h4 := mul_pos (sub_pos.mpr htr) (zpow_pos hp k)
        linarith
      rw [hzC (f t) hft1 hft2, hft]
      linear_combination ((t : ℚ) - r) * hpk
    · have htr' : (r : ℚ) ≤ t := not_lt.mp htr
      obtain ⟨-, -, hfr⟩ := hf
      rw [hfr t htr', compConjHom_apply, compConjFun_of_ge m r _ htr']
  obtain ⟨u₂, hu₂⟩ := compE_surj m r ht₂
  have hceil : u₂ ≤ ((⌈u₂⌉.toNat : ℕ) : ℚ) := by
    have h1 : u₂ ≤ (⌈u₂⌉ : ℚ) := Int.le_ceil u₂
    have h2 : (⌈u₂⌉ : ℤ) ≤ ((⌈u₂⌉.toNat : ℕ) : ℤ) := Int.self_le_toNat _
    have h3 : (⌈u₂⌉ : ℚ) ≤ ((⌈u₂⌉.toNat : ℕ) : ℚ) := by exact_mod_cast h2
    linarith
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hJ : t₂ ≤ compE m r ((r : ℚ) - 1 + ((⌈u₂⌉.toNat : ℕ) : ℚ)) := by
    rw [← hu₂]
    exact (compE_strictMono m r).monotone (by linarith)
  have hg := compConjInv_mem_geoF m r hr hmem (⌈u₂⌉.toNat)
    (fun t ht => hfixh t (le_trans hJ ht))
  refine ⟨(xg m 0 ^ k)⁻¹ * compConjInv m r hmem, (geoF m).mul_mem ((geoF m).inv_mem hz) hg, ?_⟩
  rw [map_mul, map_inv, compConj_compConjInv]
  group

theorem map_compConj_eq (hr : 1 ≤ r) : (geoF m).map (compConjHom m r) = compactF m r :=
  le_antisymm (map_compConj_le_compactF m r hr) (compactF_le_map m r hr)

/-- **Brown's isomorphism** `F_{n,∞} ≅ F_{n,r}`. -/
noncomputable def geoFEquivCompactF (hr : 1 ≤ r) : geoF m ≃* compactF m r :=
  ((geoF m).equivMapOfInjective (compConjHom m r) (compConjHom_injective m r)).trans
    (MulEquiv.subgroupCongr (map_compConj_eq m r hr))

/-- **`F_{n,r}` is finitely presented.** -/
theorem compactF_isFinitelyPresented (hr : 1 ≤ r) : Group.IsFinitelyPresented (compactF m r) := by
  haveI := geoF_isFinitelyPresented m
  exact Group.IsFinitelyPresented.equiv (geoFEquivCompactF m r hr)

#audit_axioms GroupApproximation.HigmanThompson.map_compConj_eq
#audit_axioms GroupApproximation.HigmanThompson.compactF_isFinitelyPresented

end HigmanThompson
end GroupApproximation
