import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RealProjectiveSpace

/-!
# The equatorial inclusions `Sⁿ ↪ Sⁿ⁺¹` and `RPⁿ ↪ RPⁿ⁺¹`

This file builds the first piece of the cell-structure / long-exact-sequence
infrastructure for the mod-two cohomology computation of `RPⁿ`: the genuine
*equatorial inclusion*

```text
Sⁿ ↪ Sⁿ⁺¹,        RPⁿ ↪ RPⁿ⁺¹,
```

obtained from the standard isometric embedding
`EuclideanSpace ℝ (Fin (n+1)) ↪ EuclideanSpace ℝ (Fin (n+2))` that pads a vector
with a final zero coordinate (`Fin.snoc · 0`).

Implemented here:

* `inclLin n` — the padding linear map, and `inclIso n` — its upgrade to a
  genuine `LinearIsometry` (norm-preserving, via inner-product preservation);
* `sphereInclusion n : C(Sⁿ, Sⁿ⁺¹)` — the equatorial sphere inclusion, with the
  computation rule `sphereInclusion_apply_coe`, **oddness/equivariance**
  `sphereInclusion_odd`, injectivity `sphereInclusion_injective`, and the fact
  that it is a topological embedding `sphereInclusion_isEmbedding`;
* `rpInclusion n : C(RPⁿ, RPⁿ⁺¹)` — the descended projective inclusion, with the
  defining square `rpInclusion_proj` (`ī ∘ proj = proj ∘ i`), its bundled form
  `rpInclusion_comp_proj`, and injectivity `rpInclusion_injective`.

These are genuine topological objects with no placeholder content. They provide
the inclusion of the preferred CW/LES route `RPⁿ⁻¹ ↪ RPⁿ`; the induced pullback
on singular cohomology is built in `RPnInclusionCohomology.lean`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The padding linear map `EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ
(Fin (n+2))` appending a final zero coordinate, via `Fin.snoc · 0`. -/
def inclLin (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) where
  toFun x := (WithLp.equiv 2 _).symm (Fin.snoc ((WithLp.equiv 2 _) x) (0 : ℝ))
  map_add' x y := by
    ext i; refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp [Fin.snoc_castSucc]
  map_smul' c x := by
    ext i; refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp [Fin.snoc_castSucc]

@[simp]
theorem inclLin_apply_castSucc (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) : inclLin n x j.castSucc = x j := by
  simp [inclLin, Fin.snoc_castSucc]

@[simp]
theorem inclLin_apply_last (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    inclLin n x (Fin.last (n + 1)) = 0 := by
  simp [inclLin]

/-- The equatorial inclusion as a genuine `LinearIsometry`: padding by a final
zero coordinate preserves the Euclidean inner product, hence the norm. -/
def inclIso (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  (inclLin n).isometryOfInner (by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [Fin.sum_univ_castSucc]
    simp [inclLin, Fin.snoc_castSucc])

@[simp]
theorem inclIso_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    inclIso n x = inclLin n x :=
  rfl

/-- The **equatorial sphere inclusion** `Sⁿ ↪ Sⁿ⁺¹` as a bundled continuous map:
the restriction of the isometric padding embedding to the unit spheres. -/
def sphereInclusion (n : ℕ) : C(Sphere n, Sphere (n + 1)) where
  toFun x := ⟨inclIso n x.1, by
    rw [mem_sphere_zero_iff_norm, LinearIsometry.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (inclIso n).continuous.comp continuous_subtype_val

@[simp]
theorem sphereInclusion_apply_coe (n : ℕ) (x : Sphere n) :
    (sphereInclusion n x : EuclideanSpace ℝ (Fin (n + 2))) = inclIso n x.1 :=
  rfl

/-- The equatorial sphere inclusion is **odd** (antipodal-equivariant):
`i (-x) = - i x`. This is what lets it descend to projective space. -/
theorem sphereInclusion_odd (n : ℕ) (x : Sphere n) :
    sphereInclusion n (-x) = -sphereInclusion n x := by
  apply Subtype.ext
  simp

/-- The equatorial sphere inclusion is injective (it is the restriction of an
injective linear isometry). -/
theorem sphereInclusion_injective (n : ℕ) :
    Function.Injective (sphereInclusion n) := by
  intro a b h
  apply Subtype.ext
  exact (inclIso n).injective (congrArg Subtype.val h)

/-- The equatorial sphere inclusion is an isometry: it is the restriction of an
isometric padding embedding, and the subtype metrics are induced. -/
theorem sphereInclusion_isometry (n : ℕ) : Isometry (sphereInclusion n) := by
  intro a b
  rw [Subtype.edist_eq, Subtype.edist_eq]
  exact (inclIso n).isometry a.1 b.1

/-- The equatorial sphere inclusion is a topological embedding. -/
theorem sphereInclusion_isEmbedding (n : ℕ) :
    Topology.IsEmbedding (sphereInclusion n) :=
  (sphereInclusion_isometry n).isEmbedding

/-- The **projective inclusion** `RPⁿ ↪ RPⁿ⁺¹` obtained by descending the odd
equatorial sphere inclusion along the double covers. -/
def rpInclusion (n : ℕ) : C(RP n, RP (n + 1)) where
  toFun := Quotient.lift (fun x : Sphere n => proj (n + 1) (sphereInclusion n x))
    (by
      intro x y hxy
      rcases hxy with h | h
      · rw [h]
      · subst h
        show proj (n + 1) (sphereInclusion n (-y)) = proj (n + 1) (sphereInclusion n y)
        rw [sphereInclusion_odd, proj_neg])
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact (proj (n + 1)).continuous.comp (sphereInclusion n).continuous

/-- The defining commuting square of the projective inclusion, pointwise:
`ī (proj x) = proj (i x)`. -/
@[simp]
theorem rpInclusion_proj (n : ℕ) (x : Sphere n) :
    rpInclusion n (proj n x) = proj (n + 1) (sphereInclusion n x) :=
  rfl

/-- The defining commuting square of the projective inclusion, bundled:
`ī ∘ proj = proj ∘ i`. -/
theorem rpInclusion_comp_proj (n : ℕ) :
    (rpInclusion n).comp (proj n) = (proj (n + 1)).comp (sphereInclusion n) := by
  ext x
  rfl

/-- The projective inclusion `RPⁿ ↪ RPⁿ⁺¹` is injective. -/
theorem rpInclusion_injective (n : ℕ) : Function.Injective (rpInclusion n) := by
  intro a b h
  obtain ⟨x, rfl⟩ := RP.exists_rep a
  obtain ⟨y, rfl⟩ := RP.exists_rep b
  rw [rpInclusion_proj, rpInclusion_proj] at h
  rcases eq_or_eq_neg_of_proj_eq h with h' | h'
  · exact congrArg (proj n) (sphereInclusion_injective n h')
  · rw [← sphereInclusion_odd] at h'
    have hxy := sphereInclusion_injective n h'
    rw [hxy]
    exact proj_neg y

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
