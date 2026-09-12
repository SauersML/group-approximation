import GroupApproximation.GGT.HullSCRelatorSeparation2RotatingFamily

/-!
# What the family's rotations generate, and the two geometric axioms

`HullSC.RotatingData` -- the input of Hull's filling quotient -- carries an apex
*set* and a rotation *assignment*, and no index type.  So the filling layer, like
the Theorem 5.1 layer, needs no generalisation: what has to be supplied is the
three clauses of `RotatingData` that mention the family, against the apices and
rotations of `GGT/HullSCRelatorSeparation2RotatingFamily.lean`.

* `rotationNormalClosure_apexRotFamily` -- the rotations generate the normal
  closure of the **union** of the family.  Every rotation is a conjugate of an
  element of some `K lam`, and every element of every `K lam` is a rotation
  about its own apex.  This is the clause that tells the quotient what it kills,
  and it is why `HullSC.ConeOffData₂.kernel_moves` is stated against the normal
  closure of the union rather than of one subgroup.
* `isSeparated_apexOrbitFamily` -- separation of the union of the orbits, from
  separation of the translates.  It reads the `separated` field of
  `ConeOffData₂` across indices as well as within one orbit, which is exactly
  the form that field was given.
* `isVeryRotating_apexRotFamily` -- very rotation, from the corresponding field.
  A rotation about a point of the union is a conjugate of an element of one
  `K lam` about a translate of `c₀ lam`, so the field applies at that index.

Nothing here needs `hne`: it is spent entirely in making the assignment well
posed, which happened in the previous module.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u v w

section Filling

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X] {Λ : Type w}

omit [PseudoMetricSpace X] in
/-- **The rotations of the family generate the normal closure of the union.**
Every rotation is a conjugate of an element of some member, and every element of
every member is a rotation about its own apex. -/
theorem rotationNormalClosure_apexRotFamily {K : Λ → Subgroup G} {c₀ : Λ → X}
    {hnorm : ∀ (lam : Λ) (s : G), s • c₀ lam = c₀ lam →
      ∀ k ∈ K lam, s * k * s⁻¹ ∈ K lam}
    {hne : ∀ lam mu : Λ, lam ≠ mu → ∀ g g' : G, g • c₀ lam ≠ g' • c₀ mu} :
    rotationNormalClosure (apexOrbitFamily (G := G) c₀)
        (apexRotFamily K c₀ hnorm hne)
      = Subgroup.normalClosure (⋃ lam : Λ, (K lam : Set G)) := by
  haveI hnrm : (rotationNormalClosure (apexOrbitFamily (G := G) c₀)
      (apexRotFamily K c₀ hnorm hne)).Normal := by
    show (Subgroup.normalClosure
      {g : G | ∃ c ∈ apexOrbitFamily (G := G) c₀,
        g ∈ apexRotFamily K c₀ hnorm hne c}).Normal
    infer_instance
  refine le_antisymm ?_ ?_
  · show Subgroup.normalClosure
      {g : G | ∃ c ∈ apexOrbitFamily (G := G) c₀,
        g ∈ apexRotFamily K c₀ hnorm hne c}
      ≤ Subgroup.normalClosure (⋃ lam : Λ, (K lam : Set G))
    refine Subgroup.normalClosure_le_normal ?_
    rintro h ⟨c, -, hh⟩
    rcases mem_apexRotFamily.mp hh with ⟨lam, g, -, k, hk, rfl⟩ | rfl
    · have hn : (Subgroup.normalClosure (⋃ lam : Λ, (K lam : Set G))).Normal :=
        inferInstance
      refine SetLike.mem_coe.mpr (hn.conj_mem k ?_ g)
      exact Subgroup.subset_normalClosure
        (Set.mem_iUnion.mpr ⟨lam, SetLike.mem_coe.mpr hk⟩)
    · exact SetLike.mem_coe.mpr (Subgroup.one_mem _)
  · refine Subgroup.normalClosure_le_normal ?_
    intro k hk
    obtain ⟨lam, hklam⟩ := Set.mem_iUnion.mp hk
    refine SetLike.mem_coe.mpr
      (mem_rotationNormalClosure (apex_mem_apexOrbitFamily (G := G) c₀ lam) ?_)
    exact mem_apexRotFamily.mpr
      (Or.inl ⟨lam, 1, one_smul G (c₀ lam), k, hklam, by group⟩)

/-- **Separation of the union of the orbits**, from separation of the
translates.  The hypothesis is the `separated` field of
`HullSC.ConeOffData₂`, which quantifies over both indices for this reason. -/
theorem isSeparated_apexOrbitFamily {c₀ : Λ → X} {rho : ℝ}
    (hsep : ∀ (lam mu : Λ) (g g' : G), g • c₀ lam ≠ g' • c₀ mu →
      rho ≤ dist (g • c₀ lam) (g' • c₀ mu)) :
    IsSeparated (apexOrbitFamily (G := G) c₀) rho := by
  intro c hc c' hc' hcc
  obtain ⟨lam, g, rfl⟩ := mem_apexOrbitFamily.mp hc
  obtain ⟨mu, g', rfl⟩ := mem_apexOrbitFamily.mp hc'
  exact hsep lam mu g g' hcc

/-- **Very rotation for the family**, from the corresponding field of
`HullSC.ConeOffData₂`.  A rotation about a point of the union is a conjugate of
an element of one `K lam` about a translate of `c₀ lam`, so the field applies at
that index; the identity rotation is excluded by hypothesis. -/
theorem isVeryRotating_apexRotFamily {K : Λ → Subgroup G} {c₀ : Λ → X}
    {hnorm : ∀ (lam : Λ) (s : G), s • c₀ lam = c₀ lam →
      ∀ k ∈ K lam, s * k * s⁻¹ ∈ K lam}
    {hne : ∀ lam mu : Λ, lam ≠ mu → ∀ g g' : G, g • c₀ lam ≠ g' • c₀ mu}
    {delta : ℝ}
    (hvr : ∀ (lam : Λ) (g k : G), k ∈ K lam → g * k * g⁻¹ ≠ 1 → ∀ x y : X,
      20 * delta ≤ dist x (g • c₀ lam) → dist x (g • c₀ lam) ≤ 40 * delta →
        20 * delta ≤ dist y (g • c₀ lam) → dist y (g • c₀ lam) ≤ 40 * delta →
          dist ((g * k * g⁻¹) • x) y ≤ 15 * delta →
            ∀ f : ℝ → X, IsGeodesicSegment f 0 (dist x y) → f 0 = x →
              f (dist x y) = y →
                ∃ s ∈ Set.Icc (0 : ℝ) (dist x y), f s = g • c₀ lam) :
    IsVeryRotating G X delta (apexOrbitFamily (G := G) c₀)
      (apexRotFamily K c₀ hnorm hne) := by
  intro c hc h hh h1 x y hx1 hx2 hy1 hy2 hxy f hf hf0 hf1
  rcases mem_apexRotFamily.mp hh with ⟨lam, g, hg, k, hk, rfl⟩ | rfl
  · rw [← hg] at hx1 hx2 hy1 hy2 ⊢
    exact hvr lam g k hk h1 x y hx1 hx2 hy1 hy2 hxy f hf hf0 hf1
  · exact absurd rfl h1

end Filling

end HullSC
end GroupApproximation
