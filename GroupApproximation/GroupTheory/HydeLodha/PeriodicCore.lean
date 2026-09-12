import GroupApproximation.GroupTheory.HigmanThompson.CompactCoreGerms
import GroupApproximation.Meta.AxiomGuard

/-!
# The `1`-periodic copy of `F_n`

Hyde and Lodha let `F_n` act on `ℝ` `1`-periodically: on each `[k, k+1]` as the standard
action on `[0, 1]`, translated.  Here that is the injective homomorphism
`perHom m : F_{n,1} →* Equiv.Perm ℚ`, `t ↦ ⌊t⌋ + f (fract t)`, for `n = m + 2`.

* `perCore m`: the image of the compactly supported part.  Supports and images transport to the
  periodic sets `perSet U = {t | fract t ∈ U}`, so the Higman–Epstein room of the core in `(u, v)`
  becomes room of `perCore m` in `perSet (u, v)` (`perCore_room`).
* `commutator_perCore_le`: every subgroup normalized by `⁅perCore, perCore⁆` that contains a
  permutation moving `perSet (u, v)` off itself contains `⁅perCore, perCore⁆`.
* `perHom_mem_commutator_perCore_of_compactF`: the periodic copy of `F_n'` lies in
  `⁅perCore, perCore⁆`.
* `exists_commutator_compactCore_apply`: `⁅core, core⁆` acts transitively on each residue class of
  `ℤ[1/n] ∩ (0, 1)` (Hyde–Lodha, Proposition 3.5 for one point).
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

/-! ## The periodic extension -/

section PerFun

variable {m : ℕ}

/-- Elements of `F_{n,1}` map `[0, 1)` into `[0, 1)`. -/
theorem compactF_mem_Ico {f : Equiv.Perm ℚ} (hf : f ∈ compactF m 1) {s : ℚ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : 0 ≤ f s ∧ f s < 1 := by
  have hmono := compactF_strictMono hf
  have h0 : f 0 = 0 := compactF_fix_nonpos hf le_rfl
  have h1 : f 1 = 1 := compactF_fix_one hf le_rfl
  constructor
  · have h := hmono.monotone hs0
    rwa [h0] at h
  · have h := hmono hs1
    rwa [h1] at h

/-- The periodic extension `t ↦ ⌊t⌋ + f (fract t)`. -/
def perFun (f : Equiv.Perm ℚ) (t : ℚ) : ℚ := ⌊t⌋ + f (Int.fract t)

theorem perFun_one (t : ℚ) : perFun 1 t = t := by
  simp only [perFun, Equiv.Perm.one_apply]
  exact Int.floor_add_fract t

theorem floor_perFun {f : Equiv.Perm ℚ} (hf : f ∈ compactF m 1) (t : ℚ) :
    ⌊perFun f t⌋ = ⌊t⌋ := by
  obtain ⟨h0, h1⟩ := compactF_mem_Ico hf (Int.fract_nonneg t) (Int.fract_lt_one t)
  rw [perFun, Int.floor_intCast_add, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩, add_zero]

theorem fract_perFun {f : Equiv.Perm ℚ} (hf : f ∈ compactF m 1) (t : ℚ) :
    Int.fract (perFun f t) = f (Int.fract t) := by
  obtain ⟨h0, h1⟩ := compactF_mem_Ico hf (Int.fract_nonneg t) (Int.fract_lt_one t)
  rw [perFun, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨h0, h1⟩]

theorem perFun_mul {f g : Equiv.Perm ℚ} (_hf : f ∈ compactF m 1) (hg : g ∈ compactF m 1)
    (t : ℚ) : perFun (f * g) t = perFun f (perFun g t) := by
  have h1 : perFun f (perFun g t) = ⌊t⌋ + f (g (Int.fract t)) := by
    rw [perFun, floor_perFun hg, fract_perFun hg]
  rw [h1]
  rfl

/-- The periodic extension of an element of `F_{n,1}`, as a permutation. -/
def perPerm (f : ↥(compactF m 1)) : Equiv.Perm ℚ where
  toFun := perFun (f : Equiv.Perm ℚ)
  invFun := perFun ((f : Equiv.Perm ℚ)⁻¹)
  left_inv t := by
    show perFun (f : Equiv.Perm ℚ)⁻¹ (perFun f t) = t
    rw [← perFun_mul ((compactF m 1).inv_mem f.2) f.2, inv_mul_cancel, perFun_one]
  right_inv t := by
    show perFun (f : Equiv.Perm ℚ) (perFun (f : Equiv.Perm ℚ)⁻¹ t) = t
    rw [← perFun_mul f.2 ((compactF m 1).inv_mem f.2), mul_inv_cancel, perFun_one]

end PerFun

variable (m : ℕ)

/-- **The `1`-periodic action of `F_n`.** -/
def perHom : ↥(compactF m 1) →* Equiv.Perm ℚ where
  toFun := perPerm
  map_one' := by
    ext t
    exact perFun_one t
  map_mul' f g := by
    ext t
    exact perFun_mul f.2 g.2 t

theorem perHom_apply (f : ↥(compactF m 1)) (t : ℚ) :
    perHom m f t = ⌊t⌋ + (f : Equiv.Perm ℚ) (Int.fract t) := rfl

theorem perHom_apply_of_mem (f : ↥(compactF m 1)) {t : ℚ} (h0 : 0 ≤ t) (h1 : t < 1) :
    perHom m f t = (f : Equiv.Perm ℚ) t := by
  rw [perHom_apply, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩, Int.fract_eq_self.mpr ⟨h0, h1⟩]
  simp

theorem perHom_add_int (f : ↥(compactF m 1)) (t : ℚ) (k : ℤ) :
    perHom m f (t + k) = perHom m f t + k := by
  rw [perHom_apply, perHom_apply, Int.floor_add_intCast, Int.fract_add_intCast]
  push_cast
  ring

theorem perHom_injective : Function.Injective (perHom m) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  apply Subtype.ext
  ext t
  show (f : Equiv.Perm ℚ) t = t
  by_cases h0 : t ≤ 0
  · exact compactF_fix_nonpos f.2 h0
  by_cases h1 : 1 ≤ t
  · exact compactF_fix_one f.2 h1
  have h := congrArg (fun p : Equiv.Perm ℚ => p t) hf
  simp only [Equiv.Perm.one_apply] at h
  rwa [perHom_apply_of_mem m f (not_le.mp h0).le (not_le.mp h1)] at h

/-! ## Periodic sets -/

/-- The periodic set `{t | fract t ∈ U}`. -/
def perSet (U : Set ℚ) : Set ℚ := {t | Int.fract t ∈ U}

theorem perSet_mono {U V : Set ℚ} (h : U ⊆ V) : perSet U ⊆ perSet V := fun _ ht => h ht

theorem perSet_disjoint {U V : Set ℚ} (h : Disjoint U V) : Disjoint (perSet U) (perSet V) :=
  Set.disjoint_left.mpr fun _ ht1 ht2 => Set.disjoint_left.mp h ht1 ht2

theorem supportedIn_perHom {f : ↥(compactF m 1)} {U : Set ℚ}
    (h : SupportedIn (f : Equiv.Perm ℚ) U) : SupportedIn (perHom m f) (perSet U) := by
  intro t ht
  rw [perHom_apply, h _ ht, Int.floor_add_fract]

theorem perHom_image_perSet (k : ↥(compactF m 1)) (U : Set ℚ) :
    perHom m k '' perSet U ⊆ perSet ((k : Equiv.Perm ℚ) '' U) := by
  rintro _ ⟨t, ht, rfl⟩
  show Int.fract (perHom m k t) ∈ (k : Equiv.Perm ℚ) '' U
  rw [perHom_apply, Int.fract_intCast_add,
    Int.fract_eq_self.mpr (compactF_mem_Ico k.2 (Int.fract_nonneg t) (Int.fract_lt_one t))]
  exact ⟨Int.fract t, ht, rfl⟩

/-! ## The periodic core -/

/-- The periodic copy of the compactly supported part of `F_{n,1}`. -/
def perCore : Subgroup (Equiv.Perm ℚ) :=
  ((compactCore m).subgroupOf (compactF m 1)).map (perHom m)

theorem perHom_mem_perCore {k : Equiv.Perm ℚ} (hk : k ∈ compactCore m) :
    perHom m ⟨k, compactCore_le hk⟩ ∈ perCore m :=
  ⟨⟨k, compactCore_le hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

theorem perHom_mem_commutator_perCore {x : ↥(compactF m 1)}
    (hx : (x : Equiv.Perm ℚ) ∈ ⁅compactCore m, compactCore m⁆) :
    perHom m x ∈ ⁅perCore m, perCore m⁆ := by
  have hle : ⁅compactCore m, compactCore m⁆ ≤
      ((⁅perCore m, perCore m⁆).comap (perHom m)).map (compactF m 1).subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, compactCore_le ha⟩ : ↥(compactF m 1)), ⟨b, compactCore_le hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (perHom_mem_perCore m ha) (perHom_mem_perCore m hb)
  obtain ⟨y, hy, hyx⟩ := hle hx
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

/-- The periodic copy of `F_n'` lies in `⁅perCore, perCore⁆`. -/
theorem perHom_mem_commutator_perCore_of_compactF {x : ↥(compactF m 1)}
    (hx : (x : Equiv.Perm ℚ) ∈ ⁅compactF m 1, compactF m 1⁆) :
    perHom m x ∈ ⁅perCore m, perCore m⁆ := by
  rw [commutator_compactF_eq m] at hx
  exact perHom_mem_commutator_perCore m hx

/-- **Room transports to periodic sets.** -/
theorem perCore_room {U : Set ℚ} (h : CommutatorRoom (compactCore m) U) :
    CommutatorRoom (perCore m) (perSet U) := by
  rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩
  obtain ⟨k, hk, k₂, hk₂, k₃, hk₃, U₁, U₂, U₃, h₁, h₂, h₁₂, h₁₃, d12, d13, d23, hsub⟩ :=
    h _ (Subgroup.mem_subgroupOf.mp hx₁) _ (Subgroup.mem_subgroupOf.mp hx₂)
  have hkF : k ∈ compactF m 1 := compactCore_le (commutator_le_self _ hk)
  refine ⟨perHom m ⟨k, hkF⟩, perHom_mem_commutator_perCore m hk,
    perHom m ⟨k₂, compactCore_le hk₂⟩, perHom_mem_perCore m hk₂,
    perHom m ⟨k₃, compactCore_le hk₃⟩, perHom_mem_perCore m hk₃,
    perSet U₁, perSet U₂, perSet U₃, ?_, ?_, ?_, ?_, perSet_disjoint d12, perSet_disjoint d13,
    perSet_disjoint d23, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact supportedIn_perHom m h₁
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact supportedIn_perHom m h₂
  · exact (perHom_image_perSet m _ U₁).trans (perSet_mono h₁₂)
  · exact (perHom_image_perSet m _ U₁).trans (perSet_mono h₁₃)
  · rintro t ((ht | ht) | ht)
    · exact hsub (Or.inl (Or.inl ht))
    · exact hsub (Or.inl (Or.inr ht))
    · exact hsub (Or.inr ht)

/-- **Higman–Epstein for the periodic core.** -/
theorem commutator_perCore_le (N : Subgroup (Equiv.Perm ℚ))
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅perCore m, perCore m⁆, g * n * g⁻¹ ∈ N) {f : Equiv.Perm ℚ}
    (hf : f ∈ N) {u v : ℚ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hdisp : Disjoint (f '' perSet (Set.Ioo u v)) (perSet (Set.Ioo u v))) :
    ⁅perCore m, perCore m⁆ ≤ N :=
  commutator_le_of_normal_commutator (perCore m) N hN hf hdisp
    (perCore_room m (compactCore_room hu huv hv))

/-! ## Orbits of the derived core -/

/-- `⁅core, core⁆` sends a point of `ℤ[1/n] ∩ (0, 1)` to any point of its residue class there. -/
theorem exists_commutator_compactCore_apply {x y : ℚ} (hx : ∃ M, x ∈ Grid (m + 2) M)
    (hy : ∃ M, y ∈ Grid (m + 2) M) (hres : ResEq m y x) (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) :
    ∃ p ∈ ⁅compactCore m, compactCore m⁆, p x = y := by
  obtain ⟨β, hβ1, hβ2, hβ⟩ := exists_grid_mem_Ioo (m := m) (max_lt hx1 hy1)
  have hM1 := le_max_left x y
  have hM2 := le_max_right x y
  obtain ⟨k, hk, hkx, -⟩ := exists_compactCore_mapsTo (m := m) hx hβ hy hβ hres (ResEq.refl β)
    hx0 (by linarith) hβ2 hy0 (by linarith) hβ2
  obtain ⟨c₀, d₀, hc₀, hd₀, h0c₀, hcd₀, hd₀1, hkW, -⟩ := compactCore_supportedIn₂ hk hk
  obtain ⟨c', hc'a, hc'b, hrc', hc'⟩ := exists_resEq_mem_Ioo (m := m) hc₀ hx1
  obtain ⟨d', hd'a, hd'b, hrd', hd'⟩ := exists_resEq_mem_Ioo (m := m) hd₀ hc'b
  obtain ⟨z, hz, hzc, hzd⟩ := exists_compactCore_mapsTo (m := m) hc₀ hd₀ hc' hd' hrc' hrd'
    h0c₀ hcd₀ hd₀1 (by linarith) hd'a hd'b
  refine ⟨⁅k, z⁆, Subgroup.commutator_mem_commutator hk hz, ?_⟩
  have hzx : z⁻¹ x ∉ Set.Ioo c₀ d₀ := by
    intro hmem
    have h := image_Ioo_subset (compactF_strictMono (compactCore_le hz)) c₀ d₀
      ⟨z⁻¹ x, hmem, Equiv.apply_symm_apply z x⟩
    rw [hzc, hzd] at h
    linarith [h.1]
  rw [commutatorElement_def]
  simp only [Equiv.Perm.mul_apply]
  rw [hkW.inv _ hzx, show z (z⁻¹ x) = x from Equiv.apply_symm_apply z x, hkx]

#audit_axioms GroupApproximation.HydeLodha.perHom_injective
#audit_axioms GroupApproximation.HydeLodha.commutator_perCore_le
#audit_axioms GroupApproximation.HydeLodha.perHom_mem_commutator_perCore_of_compactF
#audit_axioms GroupApproximation.HydeLodha.exists_commutator_compactCore_apply

end HydeLodha
end GroupApproximation
