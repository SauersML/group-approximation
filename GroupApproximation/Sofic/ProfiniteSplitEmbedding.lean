import GroupApproximation.Sofic.ProfiniteRetract

/-!
# Closed subgroups transported through split embeddings

A split embedding induces the full profinite topology on its image.  Hence a
profinitely closed subgroup remains profinitely closed after applying the
embedding, provided the ambient group is residually finite.  This strengthens
the range-closedness theorem in `ProfiniteRetract` and is the form needed to
iterate central HNN extensions over transported edge subgroups.
-/

namespace GroupApproximation

noncomputable section

variable {G H : Type*} [Group G] [Group H]

/-- A profinitely closed subgroup stays closed under a split embedding into a
residually finite ambient group. -/
theorem profiniteClosure_map_eq_of_split_closed
    [Group.ResiduallyFinite G]
    (i : H →* G) (r : G →* H) (hri : r.comp i = MonoidHom.id H)
    (L : Subgroup H) (hL : profiniteClosure L = L) :
    profiniteClosure (L.map i) = L.map i := by
  apply le_antisymm
  · intro x hx
    have hxrange : x ∈ profiniteClosure i.range := by
      intro Q _ _ q
      obtain ⟨y, hy, hyx⟩ := hx Q q
      obtain ⟨l, hl, hliy⟩ := hy
      refine ⟨i l, ⟨l, rfl⟩, ?_⟩
      rw [hliy]
      exact hyx
    rw [profiniteClosure_range_eq_range_of_retraction i r hri] at hxrange
    obtain ⟨h, rfl⟩ := hxrange
    have hhcl : h ∈ profiniteClosure L := by
      intro Q _ _ q
      have hximage := hx Q (q.comp r)
      obtain ⟨y, hy, hyx⟩ := hximage
      obtain ⟨l, hl, rfl⟩ := hy
      refine ⟨l, hl, ?_⟩
      have hril : r (i l) = l := by
        have := congrArg (fun f : H →* H ↦ f l) hri
        simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using this
      have hrih : r (i h) = h := by
        have := congrArg (fun f : H →* H ↦ f h) hri
        simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using this
      simpa only [MonoidHom.comp_apply, hril, hrih] using hyx
    rw [hL] at hhcl
    exact ⟨h, hhcl, rfl⟩
  · exact le_profiniteClosure (L.map i)

end

end GroupApproximation
