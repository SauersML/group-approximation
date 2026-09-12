import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationShort
import GroupApproximation.GroupTheory.HigmanThompson.CompactCoreGerms
import GroupApproximation.GroupTheory.HydeLodha.CommutatorGeneration
import GroupApproximation.GroupTheory.HydeLodha.StrictMonoTorsionFree
import GroupApproximation.Meta.AxiomGuard

/-!
# `Υ_{Γ₂}(I)'' = Υ_{Γ₂}(I)'` for `|I| < 1`

Hyde–Lodha, proof of Lemma 4.5, second part, for intervals `[a, b]` with `b - a < 1`.  The commutator
subgroup of `F = F_6` is simple and torsion-free, so it is its own commutator subgroup.  As in the first
part, `Υ_{Γ₂}([a, b]) ≅ Rstab_{F_6}([a, b]) ≅ F_6` for `0 < a < b < 1`, and conjugation by `Γ₂`
followed by an integer translation moves any grid interval of length `< 1` into `(0, 1)`.

* `commutator_eq_self_of_isSimpleGroup`: a simple subgroup `K` with `⁅K, K⁆ ≠ ⊥` equals `⁅K, K⁆`;
* `commutator_commutator_map_eq`, `commutator_commutator_eq_iff_top`,
  `commutator_commutator_top_of_mulEquiv`: `⁅⁅K, K⁆, ⁅K, K⁆⁆ = ⁅K, K⁆` is carried along injective
  homomorphisms and isomorphisms;
* `commutator_commutator_compactF`: `F'' = F'`, since `F' = ⁅Core, Core⁆` is simple and torsion-free;
* `commutator_commutator_upsilon_gammaTwo_unit`: the case `0 < a < b < 1`;
* `commutator_commutator_upsilon_gammaTwo_short`: `a < b` in `ℤ[1/6]` with `b - a < 1`, moved into
  `(0, 1)` by `exists_move_into_unit`, `map_conj_upsilon` and `upsilon_add_int`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-! ## Perfect commutator subgroups -/

theorem commutator_eq_self_of_isSimpleGroup {G : Type*} [Group G] (K : Subgroup G)
    [IsSimpleGroup ↥K] (hne : ⁅K, K⁆ ≠ ⊥) : ⁅K, K⁆ = K := by
  have hK : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : ⁅K, K⁆ = (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆).map K.subtype := by
    rw [Subgroup.map_commutator, hK]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆)
    inferInstance with h | h
  · exact (hne (by rw [hmap, h, Subgroup.map_bot])).elim
  · rw [hmap, h, hK]

theorem commutator_commutator_map_eq {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (K : Subgroup G) :
    ⁅⁅K.map f, K.map f⁆, ⁅K.map f, K.map f⁆⁆ = ⁅K.map f, K.map f⁆ ↔
      ⁅⁅K, K⁆, ⁅K, K⁆⁆ = ⁅K, K⁆ := by
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator]
  exact (Subgroup.map_injective hf).eq_iff

theorem commutator_commutator_eq_iff_top {G : Type*} [Group G] (K : Subgroup G) :
    ⁅⁅K, K⁆, ⁅K, K⁆⁆ = ⁅K, K⁆ ↔
      ⁅⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆, ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆⁆ =
        ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ := by
  have hK : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hinj : Function.Injective K.subtype := by
    intro x y h
    apply Subtype.ext
    exact h
  have h := commutator_commutator_map_eq K.subtype hinj (⊤ : Subgroup ↥K)
  rw [hK] at h
  exact h

theorem commutator_commutator_top_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆, ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆⁆ =
      ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆) :
    ⁅⁅(⊤ : Subgroup G'), (⊤ : Subgroup G')⁆, ⁅(⊤ : Subgroup G'), (⊤ : Subgroup G')⁆⁆ =
      ⁅(⊤ : Subgroup G'), (⊤ : Subgroup G')⁆ := by
  have htop : (⊤ : Subgroup G).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.surjective
  have h' := (commutator_commutator_map_eq e.toMonoidHom e.injective (⊤ : Subgroup G)).mpr h
  rw [htop] at h'
  exact h'

/-! ## `F''` and `Υ''` -/

/-- `F_{m+2}'' = F_{m+2}'`: the commutator subgroup `⁅Core, Core⁆` is simple and torsion-free, so its
commutator subgroup is nontrivial and normal, hence everything. -/
theorem commutator_commutator_compactF (m : ℕ) :
    ⁅⁅compactF m 1, compactF m 1⁆, ⁅compactF m 1, compactF m 1⁆⁆ =
      ⁅compactF m 1, compactF m 1⁆ := by
  haveI := isSimpleGroup_commutator_compactCore (m := m)
  have htf : ∀ g ∈ ⁅compactCore m, compactCore m⁆, ∀ n : ℕ, 0 < n → g ^ n = 1 → g = 1 :=
    fun g hg n hn hgn =>
      eq_one_of_pow_eq_one (compactF_strictMono (compactCore_le (commutator_le_self _ hg))) hn hgn
  rw [commutator_compactF_eq]
  exact commutator_eq_self_of_isSimpleGroup (⁅compactCore m, compactCore m⁆)
    (commutator_ne_bot_of_isSimpleGroup (⁅compactCore m, compactCore m⁆) htf)

/-- For `0 < a < b < 1` in `ℤ[1/6]`, `Υ_{Γ₂}([a, b]) ≅ Rstab_{F_6}([a, b]) ≅ F_6`, so
`Υ_{Γ₂}([a, b])'' = Υ_{Γ₂}([a, b])'`. -/
theorem commutator_commutator_upsilon_gammaTwo_unit {a b : ℚ} (ha : ∃ M, a ∈ Grid 6 M)
    (hb : ∃ M, b ∈ Grid 6 M) (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    ⁅⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆, ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆⁆ =
      ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆ := by
  obtain ⟨e₂⟩ := rstab_equiv_compactF_one (m := 4) ha hb hab
  exact (commutator_commutator_eq_iff_top (upsilon gammaTwo a b)).mpr
    (commutator_commutator_top_of_mulEquiv (e₂.symm.trans (rstabEquivUpsilon h0a hab hb1))
      ((commutator_commutator_eq_iff_top (compactF 4 1)).mp (commutator_commutator_compactF 4)))

/-- **Hyde–Lodha, Lemma 4.5, second part, `|I| < 1`**: for `a < b` in `ℤ[1/6]` with `b - a < 1`,
`Υ_{Γ₂}([a, b])'' = Υ_{Γ₂}([a, b])'`. -/
theorem commutator_commutator_upsilon_gammaTwo_short {a b : ℚ} (ha : ∃ M, a ∈ Grid 6 M)
    (hb : ∃ M, b ∈ Grid 6 M) (hab : a < b) (hba : b - a < 1) :
    ⁅⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆, ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆⁆ =
      ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆ := by
  obtain ⟨g, hg, j, hj0, hj1⟩ := exists_move_into_unit ha hb hab hba
  have hgmono := gammaTwo_strictMono hg
  obtain ⟨Ma, hMa⟩ := gammaTwo_apply_grid hg ha
  obtain ⟨Mb, hMb⟩ := gammaTwo_apply_grid hg hb
  have hgaG : ∃ M, g a + j ∈ Grid 6 M := ⟨Ma, grid_add hMa (int_mem_grid Ma j)⟩
  have hgbG : ∃ M, g b + j ∈ Grid 6 M := ⟨Mb, grid_add hMb (int_mem_grid Mb j)⟩
  have hunit := commutator_commutator_upsilon_gammaTwo_unit hgaG hgbG hj0
    (by have := hgmono hab; linarith) hj1
  rw [upsilon_add_int gammaTwo (g a) (g b) j,
    ← map_conj_upsilon qTwo_le_gammaTwo le_rfl hg a b] at hunit
  exact (commutator_commutator_map_eq (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    (upsilon gammaTwo a b)).mp hunit

#audit_axioms GroupApproximation.HydeLodha.commutator_eq_self_of_isSimpleGroup
#audit_axioms GroupApproximation.HydeLodha.commutator_commutator_compactF
#audit_axioms GroupApproximation.HydeLodha.commutator_commutator_upsilon_gammaTwo_unit
#audit_axioms GroupApproximation.HydeLodha.commutator_commutator_upsilon_gammaTwo_short

end HydeLodha
end GroupApproximation
