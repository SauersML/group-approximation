import GroupApproximation.GroupTheory.HigmanThompson.ResidueInvariance
import GroupApproximation.GroupTheory.HigmanThompson.CompactConj
import GroupApproximation.GroupTheory.HydeLodha.HigmanEpstein
import GroupApproximation.Meta.AxiomGuard

/-!
# The compactly supported part of `F_n` and its simple derived subgroup

Hyde and Lodha use Brown's theorem that `F_n'` is simple (their Theorem 3.2).  Here `F_n` is
`compactF m 1`, the piecewise linear permutations of `[0, 1]` over `(ℤ[1/n], n^ℤ)`, `n = m + 2`,
and `compactCore m` is its subgroup of elements that are the identity near `0` and near `1`.

* `exists_compactCore_mapsTo`: an element of the core sends two points `a < b` of `ℤ[1/n] ∩ (0,1)`
  to any two points `a' < b'` in the same residue classes (two moves, `PLMoves.exists_move`).
* `compactCore_room`: the core has room, in the sense of `HydeLodha.CommutatorRoom`, inside every
  open interval `(u, v) ⊆ [0, 1]`.
* `compactCore_displace`: a nontrivial element of the core moves some open interval off itself.
* `isSimpleGroup_commutator_compactCore`: `⁅core, core⁆` is simple (Higman–Epstein).
-/

namespace GroupApproximation
namespace HigmanThompson

open scoped commutatorElement
open HydeLodha

variable (m : ℕ)

/-- The elements of `F_{n,1}` that are the identity near `0` and near `1`. -/
def compactCore : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ compactF m 1 ∧ ∃ δ : ℚ, 0 < δ ∧ (∀ t : ℚ, t ≤ δ → f t = t) ∧
    ∀ t : ℚ, 1 - δ ≤ t → f t = t}
  one_mem' := ⟨(compactF m 1).one_mem, 1, one_pos, fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, δf, hδf, hf0, hf1⟩ ⟨hg, δg, hδg, hg0, hg1⟩
    have hm1 := min_le_left δf δg
    have hm2 := min_le_right δf δg
    refine ⟨(compactF m 1).mul_mem hf hg, min δf δg, lt_min hδf hδg, fun t ht => ?_,
      fun t ht => ?_⟩
    · show f (g t) = t
      rw [hg0 t (by linarith), hf0 t (by linarith)]
    · show f (g t) = t
      rw [hg1 t (by linarith), hf1 t (by linarith)]
  inv_mem' := by
    rintro f ⟨hf, δ, hδ, hf0, hf1⟩
    refine ⟨(compactF m 1).inv_mem hf, δ, hδ, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hf0 t ht]
    · rw [Equiv.Perm.inv_eq_iff_eq, hf1 t ht]

variable {m}

theorem compactCore_le : compactCore m ≤ compactF m 1 := fun _ h => h.1

theorem compactF_strictMono {f : Equiv.Perm ℚ} (hf : f ∈ compactF m 1) : StrictMono f :=
  hf.1.1

theorem compactF_fix_nonpos {f : Equiv.Perm ℚ} (hf : f ∈ compactF m 1) {t : ℚ} (ht : t ≤ 0) :
    f t = t :=
  hf.2.1 t ht

theorem compactF_fix_one {f : Equiv.Perm ℚ} (hf : f ∈ compactF m 1) {t : ℚ} (ht : 1 ≤ t) :
    f t = t :=
  hf.2.2 t (by exact_mod_cast ht)

theorem image_Ioo_subset {k : Equiv.Perm ℚ} (hk : StrictMono k) (p q : ℚ) :
    k '' Set.Ioo p q ⊆ Set.Ioo (k p) (k q) := by
  rintro _ ⟨t, ⟨h1, h2⟩, rfl⟩
  exact ⟨hk h1, hk h2⟩

/-- An element of `PLGroup` fixing `(-∞, α]` and `[β, ∞)`, `0 < α`, `β < 1`, lies in the core. -/
theorem move_mem_compactCore {h : Equiv.Perm ℚ} (hh : h ∈ PLGroup (m + 2) (powSlopes m))
    {α β : ℚ} (hα : 0 < α) (hβ : β < 1) (hlow : ∀ u, u ≤ α → h u = u)
    (hhigh : ∀ u, β ≤ u → h u = u) : h ∈ compactCore m := by
  have hm1 := min_le_left α (1 - β)
  have hm2 := min_le_right α (1 - β)
  refine ⟨⟨hh, fun t ht => hlow t (by linarith), fun t ht => hhigh t ?_⟩, min α (1 - β),
    lt_min hα (by linarith), fun t ht => hlow t (by linarith), fun t ht => hhigh t ?_⟩
  · have h1 : (1 : ℚ) ≤ t := by exact_mod_cast ht
    linarith
  · linarith

theorem exists_grid_mem_Ioo {l r : ℚ} (h : l < r) :
    ∃ y : ℚ, l < y ∧ y < r ∧ ∃ N, y ∈ Grid (m + 2) N := by
  obtain ⟨y, h1, h2, -, hy⟩ := exists_resEq_mem_Ioo (m := m) (x := 0)
    ⟨0, by simpa using int_mem_grid (m := m + 2) 0 0⟩ h
  exact ⟨y, h1, h2, hy⟩

/-- **Two points in, two points out.** -/
theorem exists_compactCore_mapsTo {a b a' b' : ℚ} (ha : ∃ M, a ∈ Grid (m + 2) M)
    (hb : ∃ M, b ∈ Grid (m + 2) M) (ha' : ∃ M, a' ∈ Grid (m + 2) M)
    (hb' : ∃ M, b' ∈ Grid (m + 2) M) (hra : ResEq m a' a) (hrb : ResEq m b' b)
    (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) (h0a' : 0 < a') (hab' : a' < b')
    (hb1' : b' < 1) :
    ∃ k ∈ compactCore m, k a = a' ∧ k b = b' := by
  obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := m) (lt_min h0a h0a')
  obtain ⟨β, hβ1, hβ2, hβ⟩ := exists_grid_mem_Ioo (m := m) (max_lt hb1 hb1')
  have hm1 := min_le_left a a'
  have hm2 := min_le_right a a'
  have hM1 := le_max_left b b'
  have hM2 := le_max_right b b'
  rcases le_or_gt a' a with haa | haa
  · obtain ⟨h₁, hh₁, h₁low, h₁high, h₁a⟩ := exists_move m hα hb hra.symm (by linarith)
      (by linarith) hab (by linarith)
    obtain ⟨h₂, hh₂, h₂low, h₂high, h₂b⟩ := exists_move m ha' hβ hrb.symm (by linarith) hab'
      (by linarith) (by linarith)
    refine ⟨h₂ * h₁, (compactCore m).mul_mem
      (move_mem_compactCore hh₂ h0a' hβ2 h₂low h₂high)
      (move_mem_compactCore hh₁ hα1 hb1 h₁low h₁high), ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, h₁a, h₂low a' le_rfl]
    · rw [Equiv.Perm.mul_apply, h₁high b le_rfl, h₂b]
  · obtain ⟨h₁, hh₁, h₁low, h₁high, h₁b⟩ := exists_move m ha hβ hrb.symm hab (by linarith)
      (by linarith) (by linarith)
    obtain ⟨h₂, hh₂, h₂low, h₂high, h₂a⟩ := exists_move m hα hb' hra.symm (by linarith)
      (by linarith) (by linarith) hab'
    refine ⟨h₂ * h₁, (compactCore m).mul_mem
      (move_mem_compactCore hh₂ hα1 hb1' h₂low h₂high)
      (move_mem_compactCore hh₁ h0a hβ2 h₁low h₁high), ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, h₁low a le_rfl, h₂a]
    · rw [Equiv.Perm.mul_apply, h₁b, h₂high b' le_rfl]

/-- Two elements of the core are supported in a common interval `(a, b)`, `0 < a < b < 1`, with
grid endpoints. -/
theorem compactCore_supportedIn₂ {g₁ g₂ : Equiv.Perm ℚ} (hg₁ : g₁ ∈ compactCore m)
    (hg₂ : g₂ ∈ compactCore m) :
    ∃ a b : ℚ, (∃ M, a ∈ Grid (m + 2) M) ∧ (∃ M, b ∈ Grid (m + 2) M) ∧ 0 < a ∧ a < b ∧
      b < 1 ∧ SupportedIn g₁ (Set.Ioo a b) ∧ SupportedIn g₂ (Set.Ioo a b) := by
  obtain ⟨-, δ₁, hδ₁, h₁0, h₁1⟩ := hg₁
  obtain ⟨-, δ₂, hδ₂, h₂0, h₂1⟩ := hg₂
  have hδ : (0 : ℚ) < min (min δ₁ δ₂) (1 / 2) := lt_min (lt_min hδ₁ hδ₂) (by norm_num)
  have hm1 := min_le_left (min δ₁ δ₂) (1 / 2)
  have hm2 := min_le_right (min δ₁ δ₂) (1 / 2)
  have hm3 := min_le_left δ₁ δ₂
  have hm4 := min_le_right δ₁ δ₂
  obtain ⟨a, ha1, ha2, ha⟩ := exists_grid_mem_Ioo (m := m) hδ
  obtain ⟨b, hb1, hb2, hb⟩ := exists_grid_mem_Ioo (m := m)
    (show 1 - min (min δ₁ δ₂) (1 / 2) < 1 by linarith)
  have hsupp : ∀ g : Equiv.Perm ℚ, ∀ δ : ℚ, min (min δ₁ δ₂) (1 / 2) ≤ δ →
      (∀ t : ℚ, t ≤ δ → g t = t) → (∀ t : ℚ, 1 - δ ≤ t → g t = t) → SupportedIn g (Set.Ioo a b) := by
    intro g δ hδle hg0 hg1 t ht
    by_cases hta : t ≤ a
    · exact hg0 t (by linarith)
    · have htb : b ≤ t := by
        by_contra htb
        exact ht ⟨not_le.mp hta, not_le.mp htb⟩
      exact hg1 t (by linarith)
  exact ⟨a, b, ha, hb, ha1, by linarith, hb2, hsupp g₁ δ₁ (by linarith) h₁0 h₁1,
    hsupp g₂ δ₂ (by linarith) h₂0 h₂1⟩

/-- **Room.**  The core has room inside every open interval `(u, v) ⊆ [0, 1]`. -/
theorem compactCore_room {u v : ℚ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    CommutatorRoom (compactCore m) (Set.Ioo u v) := by
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨a₀, b₀, ha₀, hb₀, h0a₀, hab₀, hb₀1, hs₁, hs₂⟩ := compactCore_supportedIn₂ hg₁ hg₂
  have hw : 0 < (v - u) / 8 := by linarith
  obtain ⟨p₁, hp₁a, hp₁b, hp₁⟩ :=
    exists_grid_mem_Ioo (m := m) (show u < u + (v - u) / 8 by linarith)
  obtain ⟨q₁, hq₁a, hq₁b, hq₁⟩ :=
    exists_grid_mem_Ioo (m := m) (show u + (v - u) / 8 < u + 2 * ((v - u) / 8) by linarith)
  obtain ⟨p₂, hp₂a, hp₂b, hp₂⟩ :=
    exists_grid_mem_Ioo (m := m) (show u + 2 * ((v - u) / 8) < u + 3 * ((v - u) / 8) by linarith)
  obtain ⟨q₂, hq₂a, hq₂b, hq₂⟩ :=
    exists_grid_mem_Ioo (m := m) (show u + 3 * ((v - u) / 8) < u + 4 * ((v - u) / 8) by linarith)
  obtain ⟨p₃, hp₃a, hp₃b, hp₃⟩ :=
    exists_grid_mem_Ioo (m := m) (show u + 4 * ((v - u) / 8) < u + 5 * ((v - u) / 8) by linarith)
  obtain ⟨q₃, hq₃a, hq₃b, hq₃⟩ :=
    exists_grid_mem_Ioo (m := m) (show u + 5 * ((v - u) / 8) < u + 6 * ((v - u) / 8) by linarith)
  -- `k₀` squeezes the common support into `(p₁, q₁)`
  obtain ⟨a₁, ha₁a, ha₁b, hra₁, ha₁⟩ :=
    exists_resEq_mem_Ioo (m := m) ha₀ (show p₁ < q₁ by linarith)
  obtain ⟨b₁, hb₁a, hb₁b, hrb₁, hb₁⟩ := exists_resEq_mem_Ioo (m := m) hb₀ ha₁b
  obtain ⟨k₀, hk₀, hk₀a, hk₀b⟩ := exists_compactCore_mapsTo (m := m) ha₀ hb₀ ha₁ hb₁ hra₁ hrb₁
    h0a₀ hab₀ hb₀1 (by linarith) hb₁a (by linarith)
  -- `z` moves the support of `k₀` beyond `b₀`
  obtain ⟨c₀, d₀, hc₀, hd₀, h0c₀, hcd₀, hd₀1, hk₀W, -⟩ := compactCore_supportedIn₂ hk₀ hk₀
  obtain ⟨c', hc'a, hc'b, hrc', hc'⟩ := exists_resEq_mem_Ioo (m := m) hc₀ hb₀1
  obtain ⟨d', hd'a, hd'b, hrd', hd'⟩ := exists_resEq_mem_Ioo (m := m) hd₀ hc'b
  obtain ⟨z, hz, hzc, hzd⟩ := exists_compactCore_mapsTo (m := m) hc₀ hd₀ hc' hd' hrc' hrd'
    h0c₀ hcd₀ hd₀1 (by linarith) hd'a hd'b
  have hzdisj : Disjoint (z '' Set.Ioo c₀ d₀) (Set.Ioo a₀ b₀) := by
    refine Set.disjoint_left.mpr fun t ht1 ht2 => ?_
    have h := image_Ioo_subset (compactF_strictMono (compactCore_le hz)) c₀ d₀ ht1
    rw [hzc, hzd] at h
    linarith [h.1, ht2.2]
  -- `k₂`, `k₃` move `(p₁, q₁)` into `(p₂, q₂)` and `(p₃, q₃)`
  obtain ⟨p₂', hp₂'a, hp₂'b, hrp₂, hp₂'⟩ :=
    exists_resEq_mem_Ioo (m := m) hp₁ (show p₂ < q₂ by linarith)
  obtain ⟨q₂', hq₂'a, hq₂'b, hrq₂, hq₂'⟩ := exists_resEq_mem_Ioo (m := m) hq₁ hp₂'b
  obtain ⟨k₂, hk₂, hk₂p, hk₂q⟩ := exists_compactCore_mapsTo (m := m) hp₁ hq₁ hp₂' hq₂' hrp₂ hrq₂
    (by linarith) (by linarith) (by linarith) (by linarith) hq₂'a (by linarith)
  obtain ⟨p₃', hp₃'a, hp₃'b, hrp₃, hp₃'⟩ :=
    exists_resEq_mem_Ioo (m := m) hp₁ (show p₃ < q₃ by linarith)
  obtain ⟨q₃', hq₃'a, hq₃'b, hrq₃, hq₃'⟩ := exists_resEq_mem_Ioo (m := m) hq₁ hp₃'b
  obtain ⟨k₃, hk₃, hk₃p, hk₃q⟩ := exists_compactCore_mapsTo (m := m) hp₁ hq₁ hp₃' hq₃' hrp₃ hrq₃
    (by linarith) (by linarith) (by linarith) (by linarith) hq₃'a (by linarith)
  have hsqueeze : k₀ '' Set.Ioo a₀ b₀ ⊆ Set.Ioo p₁ q₁ := by
    refine (image_Ioo_subset (compactF_strictMono (compactCore_le hk₀)) a₀ b₀).trans ?_
    rw [hk₀a, hk₀b]
    exact Set.Ioo_subset_Ioo ha₁a.le hb₁b.le
  refine ⟨⁅k₀, z⁆, Subgroup.commutator_mem_commutator hk₀ hz, k₂, hk₂, k₃, hk₃,
    Set.Ioo p₁ q₁, Set.Ioo p₂ q₂, Set.Ioo p₃ q₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conj_commutatorElement_eq hk₀W hs₁ hzdisj]
    exact (hs₁.conj k₀).mono hsqueeze
  · rw [conj_commutatorElement_eq hk₀W hs₂ hzdisj]
    exact (hs₂.conj k₀).mono hsqueeze
  · refine (image_Ioo_subset (compactF_strictMono (compactCore_le hk₂)) p₁ q₁).trans ?_
    rw [hk₂p, hk₂q]
    exact Set.Ioo_subset_Ioo hp₂'a.le hq₂'b.le
  · refine (image_Ioo_subset (compactF_strictMono (compactCore_le hk₃)) p₁ q₁).trans ?_
    rw [hk₃p, hk₃q]
    exact Set.Ioo_subset_Ioo hp₃'a.le hq₃'b.le
  · exact Set.disjoint_left.mpr fun t ht1 ht2 => by linarith [ht1.2, ht2.1]
  · exact Set.disjoint_left.mpr fun t ht1 ht2 => by linarith [ht1.2, ht2.1]
  · exact Set.disjoint_left.mpr fun t ht1 ht2 => by linarith [ht1.2, ht2.1]
  · rintro t ((ht | ht) | ht)
    · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **Displacement.**  A nontrivial element of the core moves some open interval `(u, v) ⊆ [0, 1]`
off itself. -/
theorem compactCore_displace {f : Equiv.Perm ℚ} (hf : f ∈ compactCore m) (hf1 : f ≠ 1) :
    ∃ u v : ℚ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧ Disjoint (f '' Set.Ioo u v) (Set.Ioo u v) := by
  have hF := compactCore_le hf
  have hmono := compactF_strictMono hF
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ x := by
    by_contra h
    apply hf1
    ext x
    by_contra hx
    exact h ⟨x, hx⟩
  have h0 : f 0 = 0 := compactF_fix_nonpos hF le_rfl
  have h1 : f 1 = 1 := compactF_fix_one hF le_rfl
  have hx0 : 0 < x := by
    by_contra h
    exact hx (compactF_fix_nonpos hF (not_lt.mp h))
  have hx1 : x < 1 := by
    by_contra h
    exact hx (compactF_fix_one hF (not_lt.mp h))
  have hfinv : ∀ y, f (f⁻¹ y) = y := fun y => Equiv.apply_symm_apply f y
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have hfx0 : 0 < f x := by
      have h := hmono hx0
      rwa [h0] at h
    have hxv : x < f⁻¹ ((x + f x) / 2) := by
      refine hmono.lt_iff_lt.mp ?_
      rw [hfinv]
      linarith
    have hv1 : f⁻¹ ((x + f x) / 2) ≤ 1 := by
      refine hmono.le_iff_le.mp ?_
      rw [hfinv, h1]
      linarith
    refine ⟨(x + f x) / 2, f⁻¹ ((x + f x) / 2), by linarith, by linarith, hv1, ?_⟩
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩ ht
    have h := hmono hs2
    rw [hfinv] at h
    linarith [ht.1]
  · have hfx1 : f x < 1 := by
      have h := hmono hx1
      rwa [h1] at h
    have hux : f⁻¹ ((x + f x) / 2) < x := by
      refine hmono.lt_iff_lt.mp ?_
      rw [hfinv]
      linarith
    have hu0 : 0 ≤ f⁻¹ ((x + f x) / 2) := by
      refine hmono.le_iff_le.mp ?_
      rw [hfinv, h0]
      linarith
    refine ⟨f⁻¹ ((x + f x) / 2), (x + f x) / 2, hu0, by linarith, by linarith, ?_⟩
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨s, ⟨hs1, hs2⟩, rfl⟩ ht
    have h := hmono hs1
    rw [hfinv] at h
    linarith [ht.2]

variable (m)

theorem commutator_compactCore_ne_bot : ⁅compactCore m, compactCore m⁆ ≠ ⊥ := by
  have h0grid : ∃ M, (0 : ℚ) ∈ Grid (m + 2) M := ⟨0, by simpa using int_mem_grid (m := m + 2) 0 0⟩
  obtain ⟨α, hα1, hα2, hα⟩ := exists_grid_mem_Ioo (m := m) (show (0 : ℚ) < 1 / 10 by norm_num)
  obtain ⟨y₂, hy₂1, hy₂2, hry₂, -⟩ :=
    exists_resEq_mem_Ioo (m := m) h0grid (show (1 : ℚ) / 10 < 2 / 10 by norm_num)
  obtain ⟨y₁, hy₁1, hy₁2, hry₁, -⟩ :=
    exists_resEq_mem_Ioo (m := m) h0grid (show (2 : ℚ) / 10 < 3 / 10 by norm_num)
  obtain ⟨β₂, hβ₂1, hβ₂2, hβ₂⟩ := exists_grid_mem_Ioo (m := m) (show (3 : ℚ) / 10 < 4 / 10 by norm_num)
  obtain ⟨x₁, hx₁1, hx₁2, hrx₁, -⟩ :=
    exists_resEq_mem_Ioo (m := m) h0grid (show (4 : ℚ) / 10 < 5 / 10 by norm_num)
  obtain ⟨β₁, hβ₁1, hβ₁2, hβ₁⟩ := exists_grid_mem_Ioo (m := m) (show (5 : ℚ) / 10 < 6 / 10 by norm_num)
  obtain ⟨b, hb, hblow, hbhigh, hby⟩ := exists_move m hα hβ₂ (hry₁.trans hry₂.symm)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨a, ha, halow, hahigh, hax⟩ := exists_move m hα hβ₁ (hrx₁.trans hry₁.symm)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hbcore : b ∈ compactCore m :=
    move_mem_compactCore hb (by linarith) (by linarith) hblow hbhigh
  have hacore : a ∈ compactCore m :=
    move_mem_compactCore ha (by linarith) (by linarith) halow hahigh
  intro hbot
  have hmem : ⁅b, a⁆ ∈ ⁅compactCore m, compactCore m⁆ :=
    Subgroup.commutator_mem_commutator hbcore hacore
  rw [hbot, Subgroup.mem_bot] at hmem
  have hval : ⁅b, a⁆ y₁ = y₂ := by
    rw [commutatorElement_def]
    simp only [Equiv.Perm.mul_apply]
    rw [perm_inv_eq_of_apply_eq hax, perm_inv_eq_of_apply_eq (hbhigh x₁ (by linarith)), hax, hby]
  rw [hmem, Equiv.Perm.one_apply] at hval
  linarith

/-- **`F_n'` is simple**, in its compactly supported form: `⁅core, core⁆` is a simple group. -/
theorem isSimpleGroup_commutator_compactCore : IsSimpleGroup ↥⁅compactCore m, compactCore m⁆ :=
  isSimpleGroup_commutator (compactCore m) (commutator_compactCore_ne_bot m) fun f hf hf1 => by
    obtain ⟨u, v, hu, huv, hv, hdisp⟩ := compactCore_displace (commutator_le_self _ hf) hf1
    exact ⟨Set.Ioo u v, hdisp, compactCore_room hu huv hv⟩

/-- Every subgroup normalized by `⁅core, core⁆` containing an element that moves an open interval
`(u, v) ⊆ [0, 1]` off itself contains `⁅core, core⁆`. -/
theorem commutator_compactCore_le (N : Subgroup (Equiv.Perm ℚ))
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅compactCore m, compactCore m⁆, g * n * g⁻¹ ∈ N)
    {f : Equiv.Perm ℚ} (hf : f ∈ N) {u v : ℚ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hdisp : Disjoint (f '' Set.Ioo u v) (Set.Ioo u v)) :
    ⁅compactCore m, compactCore m⁆ ≤ N :=
  commutator_le_of_normal_commutator (compactCore m) N hN hf hdisp (compactCore_room hu huv hv)

#audit_axioms GroupApproximation.HigmanThompson.compactCore_room
#audit_axioms GroupApproximation.HigmanThompson.isSimpleGroup_commutator_compactCore
#audit_axioms GroupApproximation.HigmanThompson.commutator_compactCore_le

end HigmanThompson
end GroupApproximation
