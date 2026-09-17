import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `[Γ_* : tΓ_*t⁻¹] = 8`

Manuscript `non_mf_group_notes.tex`, proof of `thm:notes-abelian-boundary`
(tex lines 2088--2096):

> choose `γ ∈ Γ_*` such that `γ t Γ_* ≠ t Γ_*`; such an element exists because
> `[Γ_* : t Γ_* t⁻¹] = 8`.

Inside the ascending HNN extension `G_*` the conjugate `tΓ_*t⁻¹` is the image of `α(Γ_*)`, the
index-eight parity sublattice subgroup (`AffineSL3Doubling.alpha_range_index`).

Main declarations:

* `conjBase` — the subgroup `tΓ_*t⁻¹` of `G_*`;
* `conjBase_eq` — `tΓ_*t⁻¹ = α(Γ_*)` inside `G_*`;
* `conjBase_le` — `tΓ_*t⁻¹ ≤ Γ_*` (the extension is ascending);
* `index_eight` — `[Γ_* : tΓ_*t⁻¹] = 8`, as `conjBase.relIndex ofGamma.range = 8`;
* `exists_translate_ne` — some `γ ∈ Γ_*` has `γ t Γ_* ≠ t Γ_*` in `X = G_*/Γ_*`.
-/

namespace GroupApproximation.Full.NN05

/-- The conjugate subgroup `t Γ_* t⁻¹ ≤ G_*`. -/
def conjBase : Subgroup Gstar :=
  (ofGamma.range).map (MulAut.conj stableLetter).toMonoidHom

/-- `t Γ_* t⁻¹` is the image of `α(Γ_*)` in `G_*`. -/
theorem conjBase_eq : conjBase = alphaStar.range.map ofGamma := by
  have hcomp :
      (MulAut.conj stableLetter).toMonoidHom.comp ofGamma = ofGamma.comp alphaStar :=
    MonoidHom.ext fun g => stableLetter_conj g
  rw [conjBase, MonoidHom.map_range, MonoidHom.map_range, hcomp]

/-- The HNN extension is ascending: `t Γ_* t⁻¹ ≤ Γ_*`. -/
theorem conjBase_le : conjBase ≤ ofGamma.range := by
  rw [conjBase_eq]
  exact Subgroup.map_le_range ofGamma _

/-- **`[Γ_* : t Γ_* t⁻¹] = 8`** (tex line 2094). -/
theorem index_eight : conjBase.relIndex ofGamma.range = 8 := by
  rw [conjBase_eq, MonoidHom.range_eq_map ofGamma,
    Subgroup.relIndex_map_map_of_injective _ _ ofGamma_injective, Subgroup.relIndex_top_right]
  exact AffineSL3Doubling.alpha_range_index

/-- **Printed consequence (tex lines 2092--2094).**  There is `γ ∈ Γ_*` with
`γ t Γ_* ≠ t Γ_*` in `X = G_*/Γ_*`; one may take the translation `γ = (e₁, 1)`. -/
theorem exists_translate_ne :
    ∃ γ : GammaStar, (QuotientGroup.mk (ofGamma γ * stableLetter) : GstarCosets) ≠
      QuotientGroup.mk stableLetter := by
  refine ⟨AffineSL3Doubling.a, fun h => ?_⟩
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (QuotientGroup.eq.mp h)
  have h1 : ofGamma (alphaStar y) = ofGamma AffineSL3Doubling.a⁻¹ := by
    rw [← stableLetter_conj, hy, map_inv]
    group
  have h3 : AffineSL3Doubling.a⁻¹ ∈ alphaStar.range :=
    MonoidHom.mem_range.mpr ⟨y, ofGamma_injective h1⟩
  have h4 : AffineSL3Doubling.a ∈ alphaStar.range := by
    have h5 := inv_mem h3
    rwa [inv_inv] at h5
  exact AffineSL3Doubling.a_not_mem_range (MonoidHom.mem_range.mp h4)

#audit_axioms conjBase_eq
#audit_axioms conjBase_le
#audit_axioms index_eight
#audit_axioms exists_translate_ne

end GroupApproximation.Full.NN05
