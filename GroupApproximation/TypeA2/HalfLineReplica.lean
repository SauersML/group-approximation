/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.GroupTheory.HigmanThompson.CompactConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Periodic replicas of the interval group on the half-line

For `w ∈ compactF m 1`, which fixes `(-∞, 0]` and `[1, ∞)`, the **replica**
`replica w : t ↦ ⌊t⌋ + w (fract t)` repeats `w` on every interval `[n, n + 1]`.

* `replicaHom m : compactF m 1 →* Equiv.Perm ℚ` is a homomorphism.
* `replica_mem_PLGroup`: a replica is piecewise linear over `(ℤ[1/(m+2)], (m+2)^ℤ)`.
* `replica_mem_normalizer`: a replica normalizes `geoF m`, so conjugation gives
  `replicaNormalizerHom m : compactF m 1 →* Subgroup.normalizer (geoF m : Set (Equiv.Perm ℚ))`.
* `replica_mapsTo_posGrid`: a replica maps the positive grid points `posGrid m` into
  themselves.
* `replica_fixes_of_mul_fixes` (**germ lemma**): if `γ * replica w` fixes `posGrid m`
  pointwise for some `γ ∈ geoF m`, then so does `replica w`.  Far out, `γ` is a
  translation by an integer and a replica commutes with integer translations.
* `eq_one_of_replica_fixes`: if `replica w` fixes `posGrid m` pointwise, then `w = 1`.
  The grid points are dense and `w` is piecewise linear.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation.TypeA2

open HigmanThompson

variable {m : ℕ}

/-- The positive grid points `ℚ_{>0} ∩ ℤ[1/(m+2)]`. -/
def posGrid (m : ℕ) : Set ℚ := {t | 0 < t ∧ ∃ M : ℕ, t ∈ Grid (m + 2) M}

theorem mem_posGrid {t : ℚ} : t ∈ posGrid m ↔ 0 < t ∧ ∃ M : ℕ, t ∈ Grid (m + 2) M := Iff.rfl

/-- The function underlying a replica: `t ↦ ⌊t⌋ + w (fract t)`. -/
noncomputable def replicaFun (w : ℚ → ℚ) (t : ℚ) : ℚ := ⌊t⌋ + w (Int.fract t)

theorem replicaFun_add_intCast (w : ℚ → ℚ) (t : ℚ) (c : ℤ) :
    replicaFun w (t + c) = replicaFun w t + c := by
  unfold replicaFun
  rw [Int.floor_add_intCast, Int.fract_add_intCast]
  push_cast
  ring

section Compact

variable {w : Equiv.Perm ℚ}

theorem compactF_one_mapsTo (hw : w ∈ compactF m 1) {u : ℚ} (h0 : 0 ≤ u) (h1 : u < 1) :
    0 ≤ w u ∧ w u < 1 := by
  have hmono : StrictMono w := hw.1.1
  have e0 : w 0 = 0 := hw.2.1 0 le_rfl
  have e1 : w 1 = 1 := hw.2.2 1 (by norm_num)
  refine ⟨?_, ?_⟩
  · have := hmono.monotone h0
    rwa [e0] at this
  · have := hmono h1
    rwa [e1] at this

theorem replicaFun_eq_of_mem (hw : w ∈ compactF m 1) (n : ℤ) {x : ℚ} (h1 : (n : ℚ) ≤ x)
    (h2 : x ≤ n + 1) : replicaFun w x = n + w (x - n) := by
  rcases h2.lt_or_eq with h2 | h2
  · have hfl : ⌊x⌋ = n := Int.floor_eq_iff.mpr ⟨h1, h2⟩
    rw [replicaFun, ← Int.self_sub_floor x, hfl]
  · have hfl : ⌊x⌋ = n + 1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hfr : Int.fract x = 0 := by
      rw [← Int.self_sub_floor x, hfl, h2]
      push_cast
      ring
    have e0 : w 0 = 0 := hw.2.1 0 le_rfl
    have e1 : w 1 = 1 := hw.2.2 1 (by norm_num)
    have hx1 : x - n = 1 := by rw [h2]; ring
    rw [replicaFun, hfl, hfr, hx1, e0, e1]
    push_cast
    ring

theorem floor_replicaFun (hw : w ∈ compactF m 1) (t : ℚ) : ⌊replicaFun w t⌋ = ⌊t⌋ := by
  obtain ⟨h0, h1⟩ := compactF_one_mapsTo hw (Int.fract_nonneg t) (Int.fract_lt_one t)
  rw [Int.floor_eq_iff]
  unfold replicaFun
  constructor <;> linarith

theorem fract_replicaFun (hw : w ∈ compactF m 1) (t : ℚ) :
    Int.fract (replicaFun w t) = w (Int.fract t) := by
  rw [← Int.self_sub_floor (replicaFun w t), floor_replicaFun hw]
  unfold replicaFun
  ring

theorem replicaFun_replicaFun (hw : w ∈ compactF m 1) (v : ℚ → ℚ) (t : ℚ) :
    replicaFun v (replicaFun w t) = ⌊t⌋ + v (w (Int.fract t)) := by
  show ((⌊replicaFun w t⌋ : ℤ) : ℚ) + v (Int.fract (replicaFun w t)) = _
  rw [floor_replicaFun hw, fract_replicaFun hw]

theorem replicaFun_inv_replicaFun (hw : w ∈ compactF m 1) (t : ℚ) :
    replicaFun ⇑w⁻¹ (replicaFun w t) = t := by
  rw [replicaFun_replicaFun hw, perm_inv_apply_self, Int.floor_add_fract]

theorem replicaFun_replicaFun_inv (hw : w ∈ compactF m 1) (t : ℚ) :
    replicaFun w (replicaFun ⇑w⁻¹ t) = t := by
  rw [replicaFun_replicaFun ((compactF m 1).inv_mem hw), perm_apply_inv_self, Int.floor_add_fract]

/-- The replica of `w ∈ compactF m 1`: the permutation `t ↦ ⌊t⌋ + w (fract t)`. -/
noncomputable def replica (hw : w ∈ compactF m 1) : Equiv.Perm ℚ where
  toFun := replicaFun w
  invFun := replicaFun ⇑w⁻¹
  left_inv := replicaFun_inv_replicaFun hw
  right_inv := replicaFun_replicaFun_inv hw

theorem replica_apply (hw : w ∈ compactF m 1) (t : ℚ) : replica hw t = replicaFun w t := rfl

theorem replica_inv (hw : w ∈ compactF m 1) :
    (replica hw)⁻¹ = replica ((compactF m 1).inv_mem hw) :=
  Equiv.ext fun _ => rfl

theorem replicaFun_intCast (hw : w ∈ compactF m 1) (n : ℤ) : replicaFun w n = n := by
  have e0 : w 0 = 0 := hw.2.1 0 le_rfl
  rw [replicaFun, Int.floor_intCast, Int.fract_intCast, e0, add_zero]

theorem replicaFun_zero (hw : w ∈ compactF m 1) : replicaFun w 0 = 0 := by
  simpa using replicaFun_intCast hw 0

theorem sub_one_lt_replicaFun (hw : w ∈ compactF m 1) (t : ℚ) : t - 1 < replicaFun w t := by
  obtain ⟨h0, -⟩ := compactF_one_mapsTo hw (Int.fract_nonneg t) (Int.fract_lt_one t)
  have := Int.sub_one_lt_floor t
  unfold replicaFun
  linarith

theorem replicaFun_strictMono (hw : w ∈ compactF m 1) : StrictMono (replicaFun w) := by
  intro s t hst
  rcases (Int.floor_mono hst.le).lt_or_eq with hlt | heq
  · obtain ⟨-, hs1⟩ := compactF_one_mapsTo hw (Int.fract_nonneg s) (Int.fract_lt_one s)
    obtain ⟨ht0, -⟩ := compactF_one_mapsTo hw (Int.fract_nonneg t) (Int.fract_lt_one t)
    have h2 : ⌊s⌋ + 1 ≤ ⌊t⌋ := by omega
    have h3 : ((⌊s⌋ : ℤ) : ℚ) + 1 ≤ ⌊t⌋ := by exact_mod_cast h2
    unfold replicaFun
    linarith
  · have hfr : Int.fract s < Int.fract t := by
      rw [← Int.self_sub_floor s, ← Int.self_sub_floor t, heq]
      linarith
    have hwm : w (Int.fract s) < w (Int.fract t) := hw.1.1 hfr
    unfold replicaFun
    rw [heq]
    linarith

/-- A replica is piecewise linear at the same grid levels as `w`. -/
theorem replicaFun_gridAffine (hw : w ∈ compactF m 1) {N B : ℕ}
    (hf : GridAffine (m + 2) (powSlopes m) w N B) :
    GridAffine (m + 2) (powSlopes m) (replicaFun w) N B := by
  have hshift : ∀ k n : ℤ, gridPt (m + 2) N k - n =
      gridPt (m + 2) N (k - n * ((m + 2 : ℕ) : ℤ) ^ N) := by
    intro k n
    have hp : ((m + 2 : ℕ) : ℚ) ^ N ≠ 0 := (mPow_pos (m := m + 2) N).ne'
    unfold gridPt
    rw [eq_div_iff hp, sub_mul, div_mul_cancel₀ _ hp]
    push_cast
    ring
  have hbr : ∀ k : ℤ, ∃ n : ℤ, (n : ℚ) ≤ gridPt (m + 2) N k ∧ gridPt (m + 2) N k < n + 1 ∧
      gridPt (m + 2) N (k + 1) ≤ n + 1 := by
    intro k
    refine ⟨⌊gridPt (m + 2) N k⌋, Int.floor_le _, Int.lt_floor_add_one _, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hq : (((⌊gridPt (m + 2) N k⌋ + 1 : ℤ)) : ℚ) ∈ Grid (m + 2) N := int_mem_grid N _
    push_cast at hq
    exact not_between_consecutive hq ⟨Int.lt_floor_add_one _, hlt⟩
  refine ⟨fun k => ?_, fun k => ?_⟩
  · obtain ⟨n, hn1, hn2, hn3⟩ := hbr k
    obtain ⟨s, hsΩ, hsB, haff⟩ := hf.slope (k - n * ((m + 2 : ℕ) : ℤ) ^ N)
    refine ⟨s, hsΩ, hsB, fun x hx1 hx2 => ?_⟩
    have e1 := hshift k n
    have e2 : gridPt (m + 2) N (k - n * ((m + 2 : ℕ) : ℤ) ^ N + 1) =
        gridPt (m + 2) N (k + 1) - n := by
      rw [hshift (k + 1) n, sub_add_eq_add_sub]
    have hxa : (n : ℚ) ≤ x := le_trans hn1 hx1
    have hxb : x ≤ n + 1 := le_trans hx2 hn3
    have hlo : gridPt (m + 2) N (k - n * ((m + 2 : ℕ) : ℤ) ^ N) ≤ x - n := by
      rw [← e1]
      linarith
    have hhi : x - n ≤ gridPt (m + 2) N (k - n * ((m + 2 : ℕ) : ℤ) ^ N + 1) := by
      rw [e2]
      linarith
    have hx' := haff (x - n) hlo hhi
    rw [replicaFun_eq_of_mem hw n hxa hxb, replicaFun_eq_of_mem hw n hn1 hn2.le, hx', ← e1]
    ring
  · obtain ⟨n, hn1, hn2, -⟩ := hbr k
    rw [replicaFun_eq_of_mem hw n hn1 hn2.le, hshift k n]
    exact grid_add (int_mem_grid B n) (hf.value _)

theorem replica_mem_PLGroup (hw : w ∈ compactF m 1) :
    replica hw ∈ PLGroup (m + 2) (powSlopes m) := by
  have hwi : w⁻¹ ∈ compactF m 1 := (compactF m 1).inv_mem hw
  obtain ⟨N, B, hf⟩ := hw.1.2.1
  obtain ⟨Ni, Bi, hfi⟩ := hwi.1.2.1
  exact ⟨replicaFun_strictMono hw, ⟨N, B, replicaFun_gridAffine hw hf⟩,
    ⟨Ni, Bi, replicaFun_gridAffine hwi hfi⟩⟩

theorem replica_mapsTo_posGrid (hw : w ∈ compactF m 1) {t : ℚ} (ht : t ∈ posGrid m) :
    replica hw t ∈ posGrid m := by
  obtain ⟨ht0, M, hM⟩ := ht
  obtain ⟨N, B, hf⟩ := hw.1.2.1
  refine ⟨?_, B + max M N, (replicaFun_gridAffine hw hf).mapsGrid hM⟩
  have h := replicaFun_strictMono hw ht0
  rw [replicaFun_zero hw] at h
  exact h

theorem replica_conj_mem_geoF (hw : w ∈ compactF m 1) {γ : Equiv.Perm ℚ} (hγ : γ ∈ geoF m) :
    replica hw * γ * (replica hw)⁻¹ ∈ geoF m := by
  have hwi : w⁻¹ ∈ compactF m 1 := (compactF m 1).inv_mem hw
  obtain ⟨hγPL, hγ0, T, c, hγT⟩ := hγ
  have hPL := replica_mem_PLGroup hw
  refine ⟨(PLGroup (m + 2) (powSlopes m)).mul_mem
      ((PLGroup (m + 2) (powSlopes m)).mul_mem hPL hγPL) ((PLGroup (m + 2) (powSlopes m)).inv_mem hPL),
    fun t ht => ?_, T + 1, c, fun t ht => ?_⟩
  · show replicaFun w (γ (replicaFun ⇑w⁻¹ t)) = t
    have h1 : replicaFun ⇑w⁻¹ t ≤ 0 := by
      have h := (replicaFun_strictMono hwi).monotone ht
      rw [replicaFun_zero hwi] at h
      exact h
    rw [hγ0 _ h1, replicaFun_replicaFun_inv hw]
  · show replicaFun w (γ (replicaFun ⇑w⁻¹ t)) = t + c
    have h1 : (T : ℚ) ≤ replicaFun ⇑w⁻¹ t := by
      have h := sub_one_lt_replicaFun hwi t
      push_cast at ht
      linarith
    rw [hγT _ h1, replicaFun_add_intCast, replicaFun_replicaFun_inv hw]

theorem replica_mem_normalizer (hw : w ∈ compactF m 1) :
    replica hw ∈ Subgroup.normalizer (geoF m : Set (Equiv.Perm ℚ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro γ
  refine ⟨replica_conj_mem_geoF hw, fun h => ?_⟩
  have h2 := replica_conj_mem_geoF ((compactF m 1).inv_mem hw) h
  rw [← replica_inv hw, inv_inv] at h2
  have e : (replica hw)⁻¹ * (replica hw * γ * (replica hw)⁻¹) * replica hw = γ := by
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rwa [e] at h2

/-- **Germ lemma.**  If `γ ∈ geoF m` and `γ * replica w` fixes every positive grid point,
then `replica w` fixes every positive grid point. -/
theorem replica_fixes_of_mul_fixes (hw : w ∈ compactF m 1) {γ : Equiv.Perm ℚ} (hγ : γ ∈ geoF m)
    (hfix : ∀ s ∈ posGrid m, γ (replica hw s) = s) : ∀ s ∈ posGrid m, replica hw s = s := by
  obtain ⟨-, -, T, c, hγT⟩ := hγ
  have hT0 : (0 : ℚ) ≤ T := Nat.cast_nonneg T
  have hn : (((T : ℤ) + 1 : ℤ) : ℚ) ∈ posGrid m :=
    ⟨by push_cast; linarith, 0, int_mem_grid 0 _⟩
  have hc : (c : ℚ) = 0 := by
    have h1 := hfix _ hn
    rw [replica_apply, replicaFun_intCast hw] at h1
    have h2 := hγT (((T : ℤ) + 1 : ℤ) : ℚ) (by push_cast; linarith)
    linarith
  intro s hs
  obtain ⟨hs0, M, hsM⟩ := hs
  have hsn : s + (((T : ℤ) + 1 : ℤ) : ℚ) ∈ posGrid m :=
    ⟨by push_cast; linarith, M, grid_add hsM (int_mem_grid M _)⟩
  have h1 := hfix _ hsn
  rw [replica_apply, replicaFun_add_intCast] at h1
  have h3 := sub_one_lt_replicaFun hw s
  have h2 := hγT (replicaFun w s + (((T : ℤ) + 1 : ℤ) : ℚ)) (by push_cast; linarith)
  rw [h2, hc, add_zero] at h1
  rw [replica_apply]
  linarith

/-- If `replica w` fixes every positive grid point, then `w = 1`. -/
theorem eq_one_of_replica_fixes (hw : w ∈ compactF m 1)
    (hfix : ∀ s ∈ posGrid m, replica hw s = s) : w = 1 := by
  obtain ⟨N, B, hf⟩ := hw.1.2.1
  have hgrid : ∀ k : ℤ, w (gridPt (m + 2) N k) = gridPt (m + 2) N k := by
    intro k
    rcases le_or_gt (gridPt (m + 2) N k) 0 with h0 | h0
    · exact hw.2.1 _ h0
    rcases le_or_gt 1 (gridPt (m + 2) N k) with h1 | h1
    · exact hw.2.2 _ (by exact_mod_cast h1)
    have h := hfix (gridPt (m + 2) N k) ⟨h0, N, gridPt_mem N k⟩
    have hx0 : ((0 : ℤ) : ℚ) ≤ gridPt (m + 2) N k := by push_cast; linarith
    have hx1 : gridPt (m + 2) N k ≤ ((0 : ℤ) : ℚ) + 1 := by push_cast; linarith
    rw [replica_apply, replicaFun_eq_of_mem hw 0 hx0 hx1] at h
    simpa using h
  ext u
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ⌊u * ((m + 2 : ℕ) : ℚ) ^ N⌋ = k := ⟨_, rfl⟩
  have hbr := floor_bracket (m := m + 2) N u
  rw [hk] at hbr
  obtain ⟨s, -, -, haff⟩ := hf.slope k
  have hb := haff (gridPt (m + 2) N (k + 1)) (le_trans hbr.1 hbr.2.le) le_rfl
  have hu := haff u hbr.1 hbr.2.le
  rw [hgrid, hgrid] at hb
  rw [hgrid] at hu
  have hs : s = 1 := by
    have h0 : (s - 1) * (gridPt (m + 2) N (k + 1) - gridPt (m + 2) N k) = 0 := by
      linear_combination -hb
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · linarith [hbr.1, hbr.2]
  rw [hs, one_mul] at hu
  show w u = u
  linarith

end Compact

variable (m) in
/-- The replica map `compactF m 1 →* Equiv.Perm ℚ`. -/
noncomputable def replicaHom : compactF m 1 →* Equiv.Perm ℚ where
  toFun w := replica w.2
  map_one' := Equiv.ext fun t => Int.floor_add_fract t
  map_mul' v w := Equiv.ext fun t => (replicaFun_replicaFun w.2 (⇑(v : Equiv.Perm ℚ)) t).symm

theorem replicaHom_apply (w : compactF m 1) : replicaHom m w = replica w.2 := rfl

variable (m) in
/-- The replica map, with values in the normalizer of `geoF m`. -/
noncomputable def replicaNormalizerHom :
    compactF m 1 →* Subgroup.normalizer (geoF m : Set (Equiv.Perm ℚ)) :=
  (replicaHom m).codRestrict (Subgroup.normalizer (geoF m : Set (Equiv.Perm ℚ)))
    fun w => replica_mem_normalizer w.2

theorem coe_replicaNormalizerHom (w : compactF m 1) :
    ((replicaNormalizerHom m w : Subgroup.normalizer (geoF m : Set (Equiv.Perm ℚ))) :
      Equiv.Perm ℚ) = replica w.2 := rfl

end GroupApproximation.TypeA2
